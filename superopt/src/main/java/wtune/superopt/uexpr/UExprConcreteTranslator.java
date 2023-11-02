package wtune.superopt.uexpr;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import org.apache.commons.lang3.tuple.Pair;
import wtune.common.utils.NameSequence;
import wtune.sql.ast.*;
import wtune.sql.ast.constants.*;
import wtune.sql.plan.*;
import wtune.sql.schema.Column;
import wtune.sql.schema.Schema;
import wtune.superopt.uexpr.normalizer.QueryUExprICRewriter;
import wtune.superopt.uexpr.normalizer.QueryUExprNormalizer;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static wtune.common.datasource.DbSupport.MySQL;
import static wtune.common.utils.Commons.coalesce;
import static wtune.common.utils.IterableSupport.*;
import static wtune.common.utils.ListSupport.*;
import static wtune.sql.SqlSupport.parseSql;
import static wtune.sql.ast.ExprKind.*;
import static wtune.sql.ast.SqlNodeFields.Expr_Kind;
import static wtune.sql.ast.SqlNodeFields.ColName_Col;
import static wtune.sql.ast.SqlNodeFields.Name2_1;
import static wtune.sql.ast.constants.BinaryOpKind.*;
import static wtune.sql.ast.constants.LiteralKind.BOOL;
import static wtune.sql.ast.constants.LiteralKind.NULL;
import static wtune.sql.plan.PlanSupport.*;
import static wtune.superopt.uexpr.UExprSupport.*;
import static wtune.superopt.uexpr.UKind.*;
import static wtune.superopt.uexpr.UPred.PredKind.EQ;
import static wtune.superopt.uexpr.UPred.PredKind.GT;

public class UExprConcreteTranslator {
  private static final String VAR_NAME_PREFIX = "x";
  private PlanContext p0, p1;
  private Schema schema;
  private final BiMap<VALUESTable, String> VALUESTablesReg;
  private final UExprConcreteTranslationResult result;
  // Options
  private final boolean enableIntegrityConstraintRewrite;
  private final boolean explainsPredicates;

  UExprConcreteTranslator(PlanContext p0, PlanContext p1, int tweak) {
    this.p0 = p0;
    this.p1 = p1;
    assert Objects.equals(p0.schema(), p1.schema());
    this.schema = p0.schema();

    this.VALUESTablesReg = HashBiMap.create();
    this.result = new UExprConcreteTranslationResult(p0, p1);
    this.enableIntegrityConstraintRewrite = (tweak & UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE) != 0;
    this.explainsPredicates = (tweak & UEXPR_FLAG_NO_EXPLAIN_PREDICATES) == 0;
  }

  UExprConcreteTranslator(String sql0, String sql1, Schema baseSchema, int tweak) {
    this.VALUESTablesReg = HashBiMap.create();
    // Deal with sql queries with `VALUES` feature
    final VALUESTableParser parser = new VALUESTableParser(sql0, sql1, baseSchema);
    parser.parse();

    this.result = new UExprConcreteTranslationResult(p0, p1);
    this.enableIntegrityConstraintRewrite = (tweak & UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE) != 0;
    this.explainsPredicates = (tweak & UEXPR_FLAG_NO_EXPLAIN_PREDICATES) == 0;
  }

  UExprConcreteTranslationResult translate() {
    if (p0 == null || p1 == null) return null;

    final QueryTranslator translator0 = new QueryTranslator(p0, false, NameSequence.mkIndexed(VAR_NAME_PREFIX, 0));
    final QueryTranslator translator1 = new QueryTranslator(p1, true, NameSequence.mkIndexed(VAR_NAME_PREFIX, 0));

    if (hasDiffRootLimit(p0, p1) && !rootIsZeroLimit(p0) && !rootIsZeroLimit(p1))
      return null;

    if (hasDiffRootSort(p0, p1))
      return null;

    Set<UVar> boundVarSet = new HashSet<>();

    if (translator0.translate(skipSortRootNode(p0), boundVarSet)
            && translator1.translate(skipSortRootNode(p1), boundVarSet)) {
      if (rootIsZeroLimit(p0)) result.srcExpr = UConst.zero();
      if (rootIsZeroLimit(p1)) result.tgtExpr = UConst.zero();
      final UVar newOutVar = UVar.mkBase(UName.mk(VAR_NAME_PREFIX));
      result.alignOutVar(newOutVar);
      result.alignOutSchema();
      return result;
    } else {
      return null;
    }
  }

  private static boolean hasDiffRootSort(PlanContext p0, PlanContext p1) {
    // Hack Sort on the root
    if (p0.kindOf(p0.root()) == PlanKind.Sort && p1.kindOf(p1.root()) == PlanKind.Sort) {
      SortNode r0 = ((SortNode) p0.planRoot());
      SortNode r1 = ((SortNode) p1.planRoot());
      return !r0.toString().equals(r1.toString());
    }
    return false;
  }

  private static boolean hasDiffRootLimit(PlanContext p0, PlanContext p1) {
    // Hack Sort on the root
    boolean has0 = p0.kindOf(p0.root()) == PlanKind.Limit;
    boolean has1 = p1.kindOf(p1.root()) == PlanKind.Limit;
    if (has0 != has1){
      return true;
    }

    if (has0) {
      LimitNode r0 = ((LimitNode) p0.planRoot());
      LimitNode r1 = ((LimitNode) p1.planRoot());
      return !r0.toString().equals(r1.toString());
    }
    return false;
  }


  private static int skipSortRootNode(PlanContext plan) {
    // Hack Sort on the root
    int root = plan.root();
    while (plan.kindOf(root) == PlanKind.Sort || plan.kindOf(root) == PlanKind.Limit) {
      root = plan.childOf(root, 0);
    }
    return root;
  }

  private static boolean rootIsZeroLimit(PlanContext plan) {
    if (plan.kindOf(plan.root()) != PlanKind.Limit) return false;

    final SqlNode limit = ((LimitNode) plan.planRoot()).limit().template();
    return Literal.isInstance(limit) && limit.$(ExprFields.Literal_Value) == (Integer) 0;
  }

  static <T> String getFullName(T col) {
    assert col instanceof Column || col instanceof Value;
    if (col instanceof Column) {
      return ((Column) col).toString();
    } else {
      final Value value = (Value) col;
      if (value.qualification() == null) return value.name();
      else return value.toString();
    }
  }

  public class QueryTranslator {
    private final PlanContext plan;
    private final boolean isTargetSide;
    private final List<UVar> auxVars; // Auxiliary variable from outer query.
    private final NameSequence tupleVarSeq;

    private final String fraction_func_prefix = "FracFunc_";

    public static UTerm globalExpr;

    public final List<UVar> visibleVars; // visible vars in current scope.

    public final List<UVar> icFreshVars;

    private QueryTranslator(PlanContext plan, boolean isTargetSide, NameSequence tupleVarSeq) {
      this.plan = plan;
      this.isTargetSide = isTargetSide;
      this.visibleVars = new ArrayList<>(3);
      this.icFreshVars = new ArrayList<>();
      this.auxVars = new ArrayList<>(2);
      this.tupleVarSeq = tupleVarSeq;
    }

    private void debugSchema(UTerm expr) {
      List<UTerm> subTerms = expr.subTerms();
      for(UTerm subTerm : subTerms)
        debugSchema(subTerm);
      if(expr.kind() == SUMMATION) {
        USum sum = (USum) expr;
        Set<UVar> boundedVars = sum.boundedVars();
        for(UVar var : boundedVars)
          System.out.println(var + " : " + getTupleVarSchema(var));
      }
    }

    private boolean translate(int startNode, Set<UVar> boundVarSet) {
      // record the freshVars generated by normalizeWithIntegrityConstraints

      UTerm expr = tr(startNode);
      globalExpr = expr;
      if (expr == null) return false;
      expr = handleMultipleOutVar(expr);

      globalExpr = expr;
      expr = UExprSupport.preprocessExpr(expr);
      expr = UExprSupport.normalizeExpr(expr);
      globalExpr = expr;
      expr = normalizeRegroup(expr, boundVarSet);
      globalExpr = expr;
      if (enableIntegrityConstraintRewrite) {
        expr = normalizeWithIntegrityConstraints(expr);
      }
      else {
        expr = normalize(expr);
      }
      expr = commonNormalize(expr);

      final UVar outVar = tail(visibleVars);
      assert visibleVars.size() == 1;
      assert auxVars.size() == 0;
      if (!isTargetSide) {
        result.srcExpr = expr;
        result.srcOutVar = outVar;
      } else {
        result.tgtExpr = expr;
        result.tgtOutVar = outVar;
      }
      return true;
    }

    /*
     * Helper functions for translation
     */

    private record ValueVar(Value val, UVar var) {}
    /**
     * [var=concat(tuples)]
     */
    private UTerm generateConcatEqPred(UVar var, UVar[] tuples) {
      int bound = tuples.length, outColumnIndex = 0;
      List<UTerm> preds = new ArrayList<>(bound);
      // collect & sort output column vars
      List<ValueVar> valueTuples = new ArrayList<>();
      for (UVar tuple : tuples) {
        List<Value> schema = getTupleVarSchema(tuple);
        for (Value value : schema) {
          // [tupleColStr(tuple)]
          valueTuples.add(new ValueVar(value, tuple));
        }
      }
      valueTuples.sort(Comparator.comparing(a -> a.val.name()));
      // generate eq conditions
      for (ValueVar entry : valueTuples) {
        Value value = entry.val;
        UVar tuple = entry.var;
        String outColStr = "%" + outColumnIndex++;
        Column column = tryResolveColumn(isTargetSide ? p1 : p0, value);
        String tupleColStr = column == null ? value.name() : column.toString();
        // [outColStr(var) = tupleColStr(tuple)]
        UVar outCol = UVar.mkProj(UName.mk(outColStr), var);
        UVar tupleCol = UVar.mkProj(UName.mk(tupleColStr), tuple);
        preds.add(UPred.mkBinary(EQ, outCol, tupleCol));
      }
      return UMul.mk(preds);
    }

    /**
     * Handle cases where there are multiple out vars:
     * f(x1,x2...)
     * ->
     * sum{x1,x2...}(f(x1,x2...) * [x=concat(x1,x2...)])
     */
    private UTerm handleMultipleOutVar(UTerm expr) {
      UVar visibleVar = visibleVars.get(visibleVars.size() - 1);
      if (visibleVar == null) return expr;
      if (!visibleVar.is(UVar.VarKind.CONCAT) || visibleVar.args().length <= 1) return expr;
      // the out var should be CONCAT(...)
      UVar[] outTuples = visibleVar.args();
      UVar outVar = mkFreshBaseVar();
      putTupleVarSchema(outVar, getTupleVarSchema(visibleVar));
      UTerm eqPred = generateConcatEqPred(outVar, outTuples);
      if (eqPred == null) return expr;
      // success
      pop(visibleVars);
      push(visibleVars, outVar);
      return USum.mk(new HashSet<>(Arrays.asList(outTuples)),
              UMul.mk(expr, eqPred));
    }

    /**
     * Whether the projection contains output columns from the same source.
     * "SELECT A.C1, B.C1 FROM R AS A, R AS B" is such an example,
     * since A.C1 and B.C1 have the same source R.C1.
     */
    private boolean hasSameSourceColumns(List<Value> values) {
      List<Column> columns = tryResolveColumns(isTargetSide ? p1 : p0, values, true);
      if (columns == null) return false;
      for (int i = 0, bound = columns.size(); i < bound; i++) {
        for (int j = i + 1; j < bound; j++) {
          if (columns.get(i).equals(columns.get(j))) return true;
        }
      }
      return false;
    }

    /** Return the reduced schema, which eliminates unused tuples. */
    private UVar putConcatVarSchema(UVar outVar, UVar inVar, List<Value> outSchema) {
      assert outVar.is(UVar.VarKind.CONCAT) && inVar.is(UVar.VarKind.CONCAT);
      // the total output schema
      if (!isTargetSide) result.setSrcTupleVarSchema(outVar, outSchema);
      else result.setTgtTupleVarSchema(outVar, outSchema);
      ValuesRegistry registry = plan.valuesReg();
      // outVar is concatenation of outTuples
      // each outTuple has its own schema
      Map<UVar, List<Value>> outTupleSchemas = new HashMap<>();
      outer:
      // for each output value, find which outTuple it should belong to
      for (Value outValue : outSchema) {
        // find which column(s) each output value refers to
        Values refs = registry.valueRefsOf(registry.exprOf(outValue));
        if (refs.size() != 1) {
          // by default output columns are mapped to the first tuple
          // when an output column is not a direct reference to an input column
          //   it does not matter whatever tuple the output column belongs to
          //   since it is devoid of attribute name duplication
          UVar outTuple = outVar.args()[0];
          if (!outTupleSchemas.containsKey(outTuple))
            outTupleSchemas.put(outTuple, new ArrayList<>());
          List<Value> outTupleSchema = outTupleSchemas.get(outTuple);
          outTupleSchema.add(outValue);
          continue;
        }
        Value ref = refs.get(0);
        // locate which tuple the column lies in
        int tupleIndex = 0;
        for (UVar inTuple : inVar.args()) {
          assert inTuple.is(UVar.VarKind.BASE);
          if (getTupleVarSchema(inTuple).contains(ref)) {
            UVar outTuple = outVar.args()[tupleIndex];
            if (!outTupleSchemas.containsKey(outTuple))
              outTupleSchemas.put(outTuple, new ArrayList<>());
            List<Value> outTupleSchema = outTupleSchemas.get(outTuple);
            outTupleSchema.add(outValue);
            continue outer;
          }
          tupleIndex++;
        }
        assert false;
      }
      // put schemas (unused tuples are ignored)
      for (Map.Entry<UVar, List<Value>> entry : outTupleSchemas.entrySet()) {
        UVar outTuple = entry.getKey();
        List<Value> schema = entry.getValue();
        putTupleVarSchema(outTuple, schema);
      }
      Set<UVar> usedOutTuples = outTupleSchemas.keySet();
      // return the original outVar if all the tuples are used
      if (usedOutTuples.size() == outVar.args().length) return outVar;
      // single-tuple UVar should be a BASE var
      if (usedOutTuples.size() == 1) {
        return usedOutTuples.toArray(new UVar[0])[0];
      }
      // the tuple order in outVar is preserved in the returned concat UVar
      // unused tuples do not appear in the returned UVar
      UVar[] usedOutTuplesArray = new UVar[usedOutTuples.size()];
      int index = 0;
      for (UVar outTuple : outVar.args()) {
        if (usedOutTuples.contains(outTuple))
          usedOutTuplesArray[index++] = outTuple;
      }
      return UVar.mkConcatRaw(usedOutTuplesArray);
    }

    public void putTupleVarSchema(UVar var, List<Value> varSchema) {
      assert var.is(UVar.VarKind.BASE);
      if (!isTargetSide) result.setSrcTupleVarSchema(var, varSchema);
      else result.setTgtTupleVarSchema(var, varSchema);
    }

    public List<Value> getTupleVarSchema(UVar var) {
      assert var.is(UVar.VarKind.BASE) || var.is(UVar.VarKind.CONCAT);
      if (var.is(UVar.VarKind.BASE)) {
        return !isTargetSide ? result.srcTupleVarSchemaOf(var) : result.tgtTupleVarSchemaOf(var);
      } else {
        assert any(Arrays.stream(var.args()).toList(), v -> v.is(UVar.VarKind.BASE));
        assert var.args().length >= 2;
        List<Value> schema = getTupleVarSchema(var.args()[0]);
        for (int i = 1; i < var.args().length; ++i) {
          schema = concat(schema, getTupleVarSchema(var.args()[i]));
        }
        return schema;
      }
    }

    public UVar mkFreshBaseVar() {
      return UVar.mkBase(UName.mk(tupleVarSeq.next()));
    }

    public UVar mkFreshVarFrom(UVar var) {
      if (var.kind() == UVar.VarKind.BASE)
        return mkFreshBaseVar();
      if (var.kind() == UVar.VarKind.CONCAT) {
        // for each tuple in concat var, make a new tuple
        int bound = var.args().length;
        UVar[] newArgs = new UVar[bound];
        for (int i = 0; i < bound; i++)
          newArgs[i] = mkFreshBaseVar();
        return UVar.mkConcatRaw(newArgs);
      }
      assert false;
      return null;
    }

    public UVar mkFreshBaseVarUniqueName(String name) {
      return UVar.mkBase(UName.mk(name));
    }

    public UVar getVisibleVar() {
      /*  <!> This feature is for dependent subquery <!>
       * Visible variable is the concat of the free variable in current scope
       * and auxiliary variables from outer scope.*/
      final UVar var = tail(visibleVars);
      assert var != null;
      if (auxVars.size() == 0) return var;

      UVar visibleVar = var;
      for (UVar auxVar : auxVars) visibleVar = UVar.mkConcat(auxVar, visibleVar);

      return visibleVar;
    }

    public UVar mkProjVar(Value value, UVar var) {
      final Column column = tryResolveColumn(isTargetSide ? p1 : p0, value);
      final UName projFullName = UName.mk(getFullName((column != null) ? column : value));
      if (var.is(UVar.VarKind.BASE)) return UVar.mkProj(projFullName, var);
      else if (var.is(UVar.VarKind.PROJ)) return mkProjVar(value, var.args()[0]);
      // concat var
      for (UVar argVar : var.args()) {
        assert argVar.is(UVar.VarKind.BASE);
        if (getTupleVarSchema(argVar).contains(value))
          return UVar.mkProj(projFullName, argVar);
      }
      throw new IllegalArgumentException("value is not covered by the var's schema");
    }

    public UTerm replaceAllBoundedVars(UTerm expr) {
      expr = transformSubTerms(expr, this::replaceAllBoundedVars);
      if (expr.kind() != SUMMATION) return expr;

      final Set<UVar> oldVars = new HashSet<>(((USum) expr).boundedVars());
      for (UVar oldVar : oldVars) {
        final UVar newVar = mkFreshBaseVar();
        putTupleVarSchema(newVar, getTupleVarSchema(oldVar));
        expr = expr.replaceVar(oldVar, newVar, true);
      }
      return expr;
    }

    private UTerm getLeftJoinScalarQueryTerm(int nodeId) {
      if(plan.kindOf(nodeId) == PlanKind.Proj) {
        final ProjNode proj = (ProjNode) plan.nodeAt(nodeId);
        if(isSingleValueProj(proj.attrExprs())) {
          final UTerm predecessor = tr(plan.childOf(nodeId, 0));
          final UTerm newSum = USum.mk(UVar.getBaseVars(visibleVars.remove(visibleVars.size() - 1)), predecessor);
          return newSum;
        }
      }
      return null;
    }

    private UTerm mkPredicate(Expression exprCtx, SqlNode node, UVar baseVar) {
      return UExprSupport.normalizeExpr(mkPredicate0(exprCtx, node, baseVar));
    }

    private UTerm mkPredicate0(Expression exprCtx, SqlNode node, UVar baseVar) {
      ExprKind exprKind = node.$(Expr_Kind);
      switch (exprKind) {
        case Literal -> {
          final LiteralKind literalKind = node.$(ExprFields.Literal_Kind);
          switch (literalKind) {
            case BOOL -> {
              final Boolean value = (Boolean) node.$(ExprFields.Literal_Value);
              return value ? UConst.one() : UConst.zero();
            }
            case NULL -> {
              return UConst.nullVal();
            }
            default -> throw new IllegalArgumentException("Unsupported literal value type: " + literalKind);
          }
        }
        case Unary -> {
          final UTerm lhs = mkPredicate0(exprCtx, node.$(ExprFields.Unary_Expr), baseVar);
          if (lhs == null) return null;
          final UnaryOpKind unaryOpKind = node.$(ExprFields.Unary_Op);
          switch (unaryOpKind) {
            case NOT -> {
              // NOT (x IN (... NULL ...)) -> FALSE/NULL
              if (node.$(ExprFields.Unary_Expr).$(Expr_Kind) == Binary
                      && node.$(ExprFields.Unary_Expr).$(ExprFields.Binary_Op) == IN_LIST) {
                for (final SqlNode sqlNode : node.$(ExprFields.Unary_Expr).$(ExprFields.Binary_Right).$(ExprFields.Tuple_Exprs)) {
                  final ComposedUTerm tupleElementUTerm = mkValue(exprCtx, sqlNode, baseVar);
                  final UTerm rhsElementUTerm = tupleElementUTerm.toPredUTerm();
                  if (rhsElementUTerm.equals(UConst.nullVal())) {
                    return UConst.zero();
                  }
                }
              }
              return UNeg.mk(lhs);
            }
            default -> throw new IllegalArgumentException("Unsupported binary operator: " + unaryOpKind);
          }
        }
        case Binary -> {
          final BinaryOpKind binaryOpKind = node.$(ExprFields.Binary_Op);
          if (binaryOpKind.isLogic()) {
            final UTerm lhsPred = mkPredicate0(exprCtx, node.$(ExprFields.Binary_Left), baseVar);
            final UTerm rhsPred = mkPredicate0(exprCtx, node.$(ExprFields.Binary_Right), baseVar);
            switch (binaryOpKind) {
              // Logic operators
              case AND -> {
                return UMul.mk(lhsPred, rhsPred);
              }
              case OR -> {
                return USquash.mk(UAdd.mk(lhsPred, rhsPred));
              }
              default -> throw new IllegalArgumentException("Unsupported logical binary operator: " + binaryOpKind);
            }
          } else if (binaryOpKind == IS) {
            if (Literal.isInstance(node.$(ExprFields.Binary_Right))) {
              final LiteralKind rhsLiteralKind = node.$(ExprFields.Binary_Right).$(ExprFields.Literal_Kind);
              final Object rhsLiteralValue = node.$(ExprFields.Binary_Right).$(ExprFields.Literal_Value);
              if (rhsLiteralKind == NULL) {
                // `WHERE value IS NULL`
                final ComposedUTerm lhs = mkValue(exprCtx, node.$(ExprFields.Binary_Left), baseVar);
                if (lhs == null) return null;
                return ComposedUTerm.doComparatorOp(lhs, ComposedUTerm.mk(UConst.nullVal()), BinaryOpKind.IS);
              } else if (rhsLiteralKind == BOOL) {
                // `WHERE pred IS TRUE/FALSE`
                final UTerm lhs = mkPredicate(exprCtx, node.$(ExprFields.Binary_Left), baseVar);
                if (lhs == null) return null;
                return (Boolean) rhsLiteralValue ? lhs : UNeg.mk(lhs);
              }
            }
            throw new IllegalArgumentException("Unsupported rhs value of IS operator");
          } else if (binaryOpKind.isComparison()) {
            if (hasNullInArithmeticExpression(node))
              return UConst.zero();
            if (binaryOpKind == BinaryOpKind.EQUAL && Literal.isInstance(node.$(ExprFields.Binary_Right))) {
              final LiteralKind rhsLiteralKind = node.$(ExprFields.Binary_Right).$(ExprFields.Literal_Kind);
              final Object rhsLiteralValue = node.$(ExprFields.Binary_Right).$(ExprFields.Literal_Value);
              if (rhsLiteralKind == BOOL && (Boolean) rhsLiteralValue != null) {
                UTerm lhs = mkPredicate(exprCtx, node.$(ExprFields.Binary_Left), baseVar);
                if (lhs == null) return null;
                if(node.$(ExprFields.Binary_Left).$(Expr_Kind) == Case) {
                  if(lhs.kind() == ADD) {
                    final List<UTerm> subTerms = lhs.subTerms();
                    List<UTerm> outTerms = new ArrayList<>();
                    List<UTerm> newSubTerms = new ArrayList<>();
                    for(UTerm subTerm : subTerms) {
                      if(subTerm.subTerms().contains(UConst.NULL)) {
                        subTerm.subTerms().remove(UConst.NULL);
                        outTerms.add(UNeg.mk(subTerm));
                      } else {
                        newSubTerms.add(subTerm);
                      }
                    }
                    lhs = UMul.mk(UAdd.mk(newSubTerms), outTerms);
                  }
                }
                return (Boolean) rhsLiteralValue ? lhs : UNeg.mk(lhs);
              }
//              if (rhsLiteralKind == BOOL && (Boolean) rhsLiteralValue) {
//                ComposedUTerm lhs = mkValue(exprCtx, node.$(ExprFields.Binary_Left), baseVar);
//                if (lhs == null) return null;
//                return ComposedUTerm.doComparatorOp(lhs, rhs, binaryOpKind);
//              } else if (rhsLiteralKind == BOOL && !((Boolean) rhsLiteralValue)) {
//                ComposedUTerm lhs = mkValue(exprCtx, node.$(ExprFields.Binary_Left), baseVar);
//                if (lhs == null) return null;
//                return ComposedUTerm.doComparatorOp(lhs, rhs, binaryOpKind);
//              }
            }

            ComposedUTerm lhs = null, rhs = null;
            // Process minus `-`
            if (Binary.isInstance(node.$(ExprFields.Binary_Left)) &&
                node.$(ExprFields.Binary_Left).$(ExprFields.Binary_Op) == BinaryOpKind.MINUS) {
              // `a - b = c` => `a = b + c`
              final ComposedUTerm lhsLhs0 =
                  mkValue(exprCtx, node.$(ExprFields.Binary_Left).$(ExprFields.Binary_Left), baseVar);
              final ComposedUTerm lhsRhs0 =
                  mkValue(exprCtx, node.$(ExprFields.Binary_Left).$(ExprFields.Binary_Right), baseVar);
              final ComposedUTerm rhs0 = mkValue(exprCtx, node.$(ExprFields.Binary_Right), baseVar);
              if (lhsLhs0 == null || lhsRhs0 == null || rhs0 == null) return null;
              lhs = lhsLhs0;
              rhs = ComposedUTerm.doArithmeticOp(lhsRhs0, rhs0, BinaryOpKind.PLUS);
            } else if (Binary.isInstance(node.$(ExprFields.Binary_Right)) &&
                node.$(ExprFields.Binary_Right).$(ExprFields.Binary_Op) == BinaryOpKind.MINUS) {
              // `a = b - c` => `a + c = b`
              final ComposedUTerm rhsLhs0 =
                  mkValue(exprCtx, node.$(ExprFields.Binary_Right).$(ExprFields.Binary_Left), baseVar);
              final ComposedUTerm rhsRhs0 =
                  mkValue(exprCtx, node.$(ExprFields.Binary_Right).$(ExprFields.Binary_Right), baseVar);
              final ComposedUTerm lhs0 = mkValue(exprCtx, node.$(ExprFields.Binary_Left), baseVar);
              if (rhsLhs0 == null || rhsRhs0 == null || lhs0 == null) return null;
              lhs = ComposedUTerm.doArithmeticOp(rhsRhs0, lhs0, BinaryOpKind.PLUS);
              rhs = rhsLhs0;
            }
            if (lhs == null && rhs == null) {
              lhs = mkValue(exprCtx, node.$(ExprFields.Binary_Left), baseVar);
              rhs = mkValue(exprCtx, node.$(ExprFields.Binary_Right), baseVar);
            }
            if (lhs == null || rhs == null) return null;
            return ComposedUTerm.doComparatorOp(lhs, rhs, binaryOpKind);
          } else if (binaryOpKind == BinaryOpKind.IN_SUBQUERY) {
            final SqlNode inSubQuery = node.$(ExprFields.Binary_Right).$(ExprFields.QueryExpr_Query);
            final int inSubQueryRootId = plan.getSubQueryPlanRootIdBySqlNode(inSubQuery);

            final UVar lhsVisibleVar = tail(visibleVars);
            assert lhsVisibleVar != null;
            push(auxVars, lhsVisibleVar);
            final UTerm rhs = tr(inSubQueryRootId);
            pop(auxVars);
            if (rhs == null) return null;

            // rhs vars are no longer visible.
            final UVar rhsVisibleVar = pop(visibleVars);
            assert rhsVisibleVar != null;

            // Process lhs expr
            final SqlNode lhsExpr = node.$(ExprFields.Binary_Left);
            final List<ComposedUTerm> lhsExprTerms = new ArrayList<>();
            if (Tuple.isInstance(lhsExpr)) {
              for (SqlNode e : lhsExpr.$(ExprFields.Tuple_Exprs)) {
                final ComposedUTerm term = mkValue(exprCtx, e, lhsVisibleVar);
                if (term == null) return null;
                lhsExprTerms.add(term);
              }
            } else {
              final ComposedUTerm term = mkValue(exprCtx, lhsExpr, lhsVisibleVar);
              if (term == null) return null;
              lhsExprTerms.add(mkValue(exprCtx, lhsExpr, lhsVisibleVar));
            }
            if (lhsExprTerms.isEmpty()) return null;

            final UTerm eqCond = mkInSubEqCond(lhsExprTerms, rhsVisibleVar);
            final UTerm decoratedRhs = USum.mk(UVar.getBaseVars(rhsVisibleVar), UMul.mk(eqCond, rhs));
            return USquash.mk(decoratedRhs);
          }

          if (binaryOpKind == IN_LIST) {
//            final UTerm lhsPred = mkPredicate0(exprCtx, node.$(ExprFields.Binary_Left), baseVar);
            final ComposedUTerm lhsComposedUTerm = mkValue(exprCtx, node.$(ExprFields.Binary_Left), baseVar);
            final UTerm lhsUTerm = lhsComposedUTerm.toPredUTerm();
            SqlNodes rhs = node.$(ExprFields.Binary_Right).$(ExprFields.Tuple_Exprs);
            int listSize = rhs.size();

            if (!explainsPredicates && listSize > 1) {
              List<UTerm> arguments = new ArrayList<>();
              arguments.add(lhsUTerm);
              for (SqlNode sqlNode : rhs) {
                ComposedUTerm arg = mkValue(exprCtx, sqlNode, baseVar);
                arguments.add(arg.toPredUTerm());
              }
              String funcName = PredefinedFunctions.instantiateFamilyFunc(PredefinedFunctions.NAME_IN_LIST, arguments.size());
              UTerm in = UFunc.mk(UFunc.FuncKind.INTEGER, UName.mk(funcName), arguments);
              return UPred.mkBinary(GT, in, UConst.zero());
            }

            List<UTerm> OR_terms = new ArrayList<>();
            for (final SqlNode sqlNode : rhs) {
              final ComposedUTerm tupleElementUTerm = mkValue(exprCtx, sqlNode, baseVar);
              final UTerm rhsElementUTerm = tupleElementUTerm.toPredUTerm();
              OR_terms.add(UPred.mkBinary(EQ, lhsUTerm, rhsElementUTerm));
            }
            return USquash.mk(UAdd.mk(OR_terms));
          }

          if (binaryOpKind == LIKE) {
            final ComposedUTerm lhsComposedUTerm = mkValue(exprCtx, node.$(ExprFields.Binary_Left), baseVar);
            final ComposedUTerm rhsComposedUTerm = mkValue(exprCtx, node.$(ExprFields.Binary_Right), baseVar);
            if (rhsComposedUTerm.toPredUTerm() instanceof UString string) {
              String regex = "[a-zA-Z]+$";
              Pattern pattern = Pattern.compile(regex);
              Matcher matcher = pattern.matcher(string.value());
              // TODO: Only consider equal case here
              if (matcher.matches()) {
                return UPred.mkBinary(EQ, lhsComposedUTerm.toPredUTerm(), rhsComposedUTerm.toPredUTerm());
              }
            }
            // translate LIKE into an uninterpreted function
            final List<UTerm> arguments = new ArrayList<>(Arrays.asList(lhsComposedUTerm.toPredUTerm(),
                    rhsComposedUTerm.toPredUTerm()));
            UTerm like = UFunc.mk(UFunc.FuncKind.STRING, UName.mk(PredefinedFunctions.NAME_LIKE), arguments);
            return UPred.mkBinary(GT, like, UConst.zero());
          }

          throw new IllegalArgumentException("Unsupported binary operator: " + binaryOpKind);
        }
        case Ternary -> {
          // only case for Between And
          final TernaryOp ternaryOp = node.$(ExprFields.Ternary_Op);
          assert ternaryOp == TernaryOp.BETWEEN_AND;
          final ComposedUTerm lhs = mkValue(exprCtx, node.$(ExprFields.Ternary_Left), baseVar);
          final ComposedUTerm mhs = mkValue(exprCtx, node.$(ExprFields.Ternary_Middle), baseVar);
          final ComposedUTerm rhs = mkValue(exprCtx, node.$(ExprFields.Ternary_Right), baseVar);
          return UMul.mk(ComposedUTerm.doComparatorOp(lhs, mhs, GREATER_OR_EQUAL),
                          ComposedUTerm.doComparatorOp(lhs, rhs, LESS_OR_EQUAL));
        }
        case Case -> {
          final SqlNodes whens = node.$(ExprFields.Case_Whens);
          final List<UTerm> whenConds = new ArrayList<>(whens.size());
          final List<UTerm> thenExprs = new ArrayList<>(whens.size());
          for (SqlNode when : whens) {
            UTerm whenCond = mkPredicate(exprCtx, when.$(ExprFields.When_Cond), baseVar);
            if(when.$(ExprFields.When_Cond).$(Expr_Kind) == Binary
                    && when.$(ExprFields.When_Cond).$(ExprFields.Binary_Op) == OR) {
              final UTerm lhsPred = mkPredicate0(exprCtx, when.$(ExprFields.When_Cond).$(ExprFields.Binary_Left), baseVar);
              final UTerm rhsPred = mkPredicate0(exprCtx, when.$(ExprFields.When_Cond).$(ExprFields.Binary_Right), baseVar);
              if(lhsPred.equals(UConst.nullVal()) && !rhsPred.equals(UConst.nullVal())) {
                whenCond = rhsPred;
              } else if (rhsPred.equals(UConst.nullVal()) && !lhsPred.equals(UConst.nullVal())) {
                whenCond = lhsPred;
              } else if (rhsPred.equals(UConst.nullVal()) && lhsPred.equals(UConst.nullVal())) {
                whenCond = UConst.zero();
              }
            }
            final UTerm thenExpr = mkPredicate(exprCtx, when.$(ExprFields.When_Expr), baseVar);
            if (whenCond == null || thenExpr == null) return null;
            whenConds.add(whenCond);
            thenExprs.add(thenExpr);
          }
          final UTerm elseExpr = mkPredicate(exprCtx, node.$(ExprFields.Case_Else), baseVar);
          if (elseExpr == null) return null;

          assert whenConds.size() == thenExprs.size();
          final List<UTerm> caseWhenTerms = new ArrayList<>();
          for (int i = 0; i < whenConds.size(); i++) {
            final List<UTerm> preCondList = new ArrayList<>();
            for (int j = 0; j < i; j++)
              preCondList.add(UNeg.mk(whenConds.get(j).copy()));
            preCondList.add(whenConds.get(i).copy());
            final UTerm preCond = preCondList.size() == 1 ? preCondList.get(0) : UMul.mk(preCondList);
            caseWhenTerms.add(UMul.mk(preCond, thenExprs.get(i)));
          }
          final List<UTerm> elsePreCondList = new ArrayList<>();
          whenConds.forEach(c -> elsePreCondList.add(UNeg.mk(c.copy())));
          final UTerm elsePreCond = elsePreCondList.size() == 1 ? elsePreCondList.get(0) : UMul.mk(elsePreCondList);
          caseWhenTerms.add(UMul.mk(elsePreCond, elseExpr));

          return UAdd.mk(caseWhenTerms);
        }
        case Exists -> {
          final SqlNode existsSubQuery = node.$(ExprFields.Exists_Subquery).$(ExprFields.QueryExpr_Query);
          final int existsSubQueryRootId = plan.getSubQueryPlanRootIdBySqlNode(existsSubQuery);

          final UVar lhsVisibleVar = tail(visibleVars);
          assert lhsVisibleVar != null;
          push(auxVars, lhsVisibleVar);
          final UTerm rhs = tr(existsSubQueryRootId);
          pop(auxVars);
          if (rhs == null) return null;

          // Store lhs visible var and free var only, rhs vars are no longer visible.
          final UVar rhsVisibleVar = pop(visibleVars);
          assert rhsVisibleVar != null;

          return USquash.mk(USum.mk(UVar.getBaseVars(rhsVisibleVar), rhs));
        }
        case FuncCall -> {
          String functionName = node.$(ExprFields.FuncCall_Name).toString();
          if (functionName.equals("`if`")) {
            final SqlNodes args = node.$(ExprFields.FuncCall_Args);
            assert args.size() == 3;
            final UTerm condition = mkPredicate(exprCtx, args.get(0), baseVar);
            final UTerm firstCase = mkPredicate(exprCtx, args.get(1), baseVar);
            final UTerm secondCase = mkPredicate(exprCtx, args.get(2), baseVar);
            final List<UTerm> IF = new ArrayList<>();
            IF.add(UMul.mk(condition, firstCase));
            IF.add(UMul.mk(UNeg.mk(condition.copy()), secondCase));
            return UAdd.mk(IF);
          }
        }
      }
      throw new IllegalArgumentException("Unsupported SqlNode kind: " + exprKind);
    }

    private ComposedUTerm mkValue(Expression exprCtx, SqlNode node, UVar baseVar) {
      final ExprKind exprKind = node.$(Expr_Kind);
      switch (exprKind) {
        case ColRef -> {
          final int index = exprCtx.internalRefs().indexOf(node);
          if (index < 0) return null;
          final Value param = plan.valuesReg().valueRefsOf(exprCtx).get(index);
          final UVar projVar = mkProjVar(param, baseVar);
          return ComposedUTerm.mk(UVarTerm.mk(projVar));
        }
        case Literal -> {
          final LiteralKind literalKind = node.$(ExprFields.Literal_Kind);
          switch (literalKind) {
            case INTEGER -> {
              final Integer value = (Integer) node.$(ExprFields.Literal_Value);
              return ComposedUTerm.mk(UConst.mk(value));
            }
            case NULL -> {
              return ComposedUTerm.mk(UConst.nullVal());
            }
            case BOOL -> {
              final boolean value = (boolean) node.$(ExprFields.Literal_Value);
              return ComposedUTerm.mk(UConst.mk(value ? 1 : 0));
            }
            case TEXT -> {
              final String value = (String) node.$(ExprFields.Literal_Value);
              return ComposedUTerm.mk(UString.mk(value));
            }
            case FRACTIONAL -> {
              final double value = (double) node.$(ExprFields.Literal_Value);
              // TODO: handle other fractional cases
              if(value == 0) {
                return ComposedUTerm.mk(UConst.zero());
              }
              // Integer case
              if(value == Math.floor(value)) {
                return ComposedUTerm.mk(UConst.mk((int) Math.floor(value)));
              }
              UName funcName = UName.mk(fraction_func_prefix + value);
              return ComposedUTerm.mk(ComposedUTerm.mkFuncCall(UFunc.FuncKind.STRING, funcName, new ArrayList<>()));
            }
            default -> throw new IllegalArgumentException("Unsupported literal value type: " + literalKind);
          }
        }
        case Symbol -> {
          // same as Literal String
          final String value = node.$(ExprFields.Symbol_Text);
          return ComposedUTerm.mk(UString.mk(value));
        }
        case Binary -> {
          final BinaryOpKind binaryOpKind = node.$(ExprFields.Binary_Op);
          if(binaryOpKind == IN_SUBQUERY) {
            final UTerm result = mkPredicate(exprCtx, node, baseVar);
            return ComposedUTerm.mk(result);
          }
          final ComposedUTerm lhs = mkValue(exprCtx, node.$(ExprFields.Binary_Left), baseVar);
          final ComposedUTerm rhs = mkValue(exprCtx, node.$(ExprFields.Binary_Right), baseVar);
          if (lhs == null || rhs == null) return null;

          if (binaryOpKind.isArithmetic()) {
            return ComposedUTerm.doArithmeticOp(lhs, rhs, binaryOpKind);
          } else if (binaryOpKind.isComparison()) {
            return ComposedUTerm.mk(ComposedUTerm.doComparatorOp(lhs, rhs, binaryOpKind));
          } else if (isOrConcatOp(binaryOpKind, node.$(ExprFields.Binary_Left), node.$(ExprFields.Binary_Right))) {
            UName funcName = UName.mk("`concat`");
            List<ComposedUTerm> arguments =  new ArrayList<>();
            arguments.add(lhs);
            arguments.add(rhs);
            return ComposedUTerm.mk(ComposedUTerm.mkFuncCall(UFunc.FuncKind.STRING, funcName, arguments));
          } else if (binaryOpKind.isLogic()) {
            return ComposedUTerm.doLogicOp(lhs, rhs, binaryOpKind);
          }
        }
        case Unary -> {
          final UnaryOpKind unaryOpKind = node.$(ExprFields.Unary_Op);
          final ComposedUTerm rhs = mkValue(exprCtx, node.$(ExprFields.Unary_Expr), baseVar);
          if (rhs == null ) return null;

          return ComposedUTerm.doUnaryOp(rhs, unaryOpKind);
        }
        case Case -> {
          final SqlNodes whens = node.$(ExprFields.Case_Whens);
          final List<UTerm> whenConds = new ArrayList<>(whens.size());
          final List<ComposedUTerm> thenExprs = new ArrayList<>(whens.size());
          for (SqlNode when : whens) {
            final UTerm whenCond = mkPredicate(exprCtx, when.$(ExprFields.When_Cond), baseVar);
            if (whenCond instanceof UPred && ((UPred)whenCond).isTruePred(globalExpr) == 0) continue;
            final ComposedUTerm thenExpr = mkValue(exprCtx, when.$(ExprFields.When_Expr), baseVar);
            if (whenCond == null || thenExpr == null) return null;
            whenConds.add(whenCond);
            thenExprs.add(thenExpr);
          }
          final ComposedUTerm elseExpr = mkValue(exprCtx, node.$(ExprFields.Case_Else), baseVar);
          if (elseExpr == null) return null;
          assert whenConds.size() == thenExprs.size();
          final ComposedUTerm caseWhen = ComposedUTerm.mk();
          for (int i = 0; i < whenConds.size(); i++) {
            final List<UTerm> preCondList = new ArrayList<>();
            for (int j = 0; j < i; j++)
              preCondList.add(UNeg.mk(whenConds.get(j).copy()));
            preCondList.add(whenConds.get(i).copy());
            final UTerm preCond = preCondList.size() == 1 ? preCondList.get(0) : UMul.mk(preCondList);
            caseWhen.appendTermPair(preCond, thenExprs.get(i).toPredUTerm());
          }
          final List<UTerm> elsePreCondList = new ArrayList<>();
          whenConds.forEach(c -> elsePreCondList.add(UNeg.mk(c.copy())));
          UTerm elsePreCond = null;
          switch (elsePreCondList.size()) {
            case 0: {
              ArrayList<UTerm> args = new ArrayList<>();
              args.add(UConst.ZERO);
              args.add(UConst.ZERO);
                elsePreCond = UPred.mk(EQ, UName.mk("="), args);
              break;
            }
            case 1: {
              elsePreCond = elsePreCondList.get(0);
              break;
            }
            default: {
              elsePreCond = UMul.mk(elsePreCondList);
            }
          }
          caseWhen.appendTermPair(elsePreCond, elseExpr.toPredUTerm());
          return caseWhen;
        }
        case FuncCall -> {
          String functionName = node.$(ExprFields.FuncCall_Name).toString();
          if(functionName.equals("`positive`")) {
            final SqlNodes args = node.$(ExprFields.FuncCall_Args);
            assert(args.size() == 1);
            return mkValue(exprCtx, args.get(0), baseVar);
          }
          if(functionName.equals("`power`")) {
            final SqlNodes args = node.$(ExprFields.FuncCall_Args);
            assert(args.size() == 2);
            if(args.get(1).$(Expr_Kind) == Literal && (double) args.get(1).$(ExprFields.Literal_Value) == 0.5) {
              UName funcName = UName.mk("sqrt");
              List<ComposedUTerm> arguments =  new ArrayList<>();
              arguments.add(mkValue(exprCtx, args.get(0), baseVar));
              return ComposedUTerm.mk(ComposedUTerm.mkFuncCall(UFunc.FuncKind.INTEGER, funcName, arguments));
            }
            throw new IllegalArgumentException("Unsupported SqlNode UFunc power");
          }
          if(functionName.equals("`single_value`")) {
            final SqlNodes args = node.$(ExprFields.FuncCall_Args);
            return mkValue(exprCtx, args.get(0), baseVar);
          }
          if(functionName.equals("`if`")) {
            final SqlNodes args = node.$(ExprFields.FuncCall_Args);
            assert args.size() == 3;
            final ComposedUTerm condition = mkValue(exprCtx, args.get(0), baseVar);
            final ComposedUTerm firstCase = mkValue(exprCtx, args.get(1), baseVar);
            final ComposedUTerm secondCase = mkValue(exprCtx, args.get(2), baseVar);
            final ComposedUTerm IF = ComposedUTerm.mk();
            IF.appendTermPair(condition.toPredUTerm(), firstCase.toPredUTerm());
            IF.appendTermPair(UNeg.mk(condition.toPredUTerm().copy()), secondCase.toPredUTerm());
            if(condition.toPredUTerm().equals(UConst.nullVal()))
              return secondCase;
            return IF;
          }
          UName funcName = UName.mk(functionName);
          List<ComposedUTerm> arguments =  new ArrayList<>();
          for(final SqlNode arg : node.$(ExprFields.FuncCall_Args)) {
            final ComposedUTerm ahs = mkValue(exprCtx, arg, baseVar);
            arguments.add(ahs);
          }
          return ComposedUTerm.mk(ComposedUTerm.mkFuncCall(UFunc.FuncKind.STRING, funcName, arguments));
        }
        case QueryExpr -> {
          final SqlNode attrSubQuery = node.$(ExprFields.QueryExpr_Query);
          final int attrSubQueryRootId = plan.getSubQueryPlanRootIdBySqlNode(attrSubQuery);
          UTerm firstPredArg = tr(attrSubQueryRootId);
          UVar firstOutVar = visibleVars.remove(visibleVars.size() - 1);
          final List<Value> outputValues = plan.valuesReg().valuesOf(attrSubQueryRootId);
          assert(outputValues.size() == 1);
          UTerm secondPredArg = tr(plan.childOf(attrSubQueryRootId, 0));
          UVar secondOutVar = visibleVars.remove(visibleVars.size() - 1);
          USum secondPredArgSum = USum.mk(Set.of(secondOutVar), secondPredArg);
          UTerm firstAddArg = UMul.mk(UPred.mkBinary(EQ, firstPredArg, UConst.one()), UPred.mkBinary(EQ, secondPredArgSum.copy(), UConst.one()));
//          secondPredArg.
          UTerm secondAddArg = UMul.mk(mkIsNullPred(mkProjVar(outputValues.get(0), firstOutVar)), UPred.mkBinary(EQ, secondPredArgSum.copy(), UConst.zero()));
          return ComposedUTerm.mk(UAdd.mk(firstAddArg, secondAddArg), mkProjVar(outputValues.get(0), firstOutVar));
        }
      }
      throw new IllegalArgumentException("Unsupported SqlNode kind: " + exprKind);
    }

    private static boolean hasNullInArithmeticExpression(SqlNode node) {
      if (colIsNullPredicate(node)) return false; // `WHERE col IS NULL`

      if (Literal.isInstance(node) && node.$(ExprFields.Literal_Kind) == LiteralKind.NULL)
        return true;

      if (Unary.isInstance(node))
        return hasNullInArithmeticExpression(node.$(ExprFields.Unary_Expr));
      if (Binary.isInstance(node))
        return hasNullInArithmeticExpression(node.$(ExprFields.Binary_Left))
            || hasNullInArithmeticExpression(node.$(ExprFields.Binary_Right));

      return false;
    }

    private static boolean isConcatOp(BinaryOpKind opKind) {
      return opKind == BinaryOpKind.CONCAT;
    }

    private static boolean isOrConcatOp(BinaryOpKind opKind, SqlNode leftChild, SqlNode rightChild) {
      if(opKind == BinaryOpKind.OR) {
        final ExprKind leftKind = leftChild.$(Expr_Kind);
        final ExprKind rightKind = rightChild.$(Expr_Kind);
        if(leftKind == FuncCall && rightKind == FuncCall) {
          if(leftChild.$(ExprFields.FuncCall_Name).toString().equals("`substring`") &&
                  rightChild.$(ExprFields.FuncCall_Name).toString().equals("`substring`"));
          return true;
        }
      }
      return false;
    }

    private static UPred.PredKind castBinaryOp2UPredOp(BinaryOpKind opKind) {
      return switch (opKind) {
        case EQUAL -> EQ;
        case NOT_EQUAL -> UPred.PredKind.NEQ;
        case LESS_THAN -> UPred.PredKind.LT;
        case LESS_OR_EQUAL -> UPred.PredKind.LE;
        case GREATER_THAN -> UPred.PredKind.GT;
        case GREATER_OR_EQUAL -> UPred.PredKind.GE;
        default -> throw new IllegalArgumentException("Unsupported binary operator: " + opKind);
      };
    }

    /**
     * Translation functions for each operator
     */
    private UTerm tr(int nodeId) {
      return switch (plan.kindOf(nodeId)) {
        case Input -> trInput(nodeId);
        case Filter -> trFilter(nodeId);
        case InSub -> trInSubFilter(nodeId);
        case Exists -> trExistsFilter(nodeId);
        case Proj -> trProj(nodeId);
        case Join -> trJoin(nodeId);
        case SetOp -> trSetOp(nodeId);
        case Agg -> trAgg(nodeId);
        case Limit -> trLimit(nodeId);
        case Sort -> trSort(nodeId);
        default -> throw new IllegalArgumentException("unknown op");
      };
    }

    private UTerm trInput(int nodeId) {
      final InputNode input = (InputNode) plan.nodeAt(nodeId);
      final String tableName = input.table().name();
      final VALUESTable VALUESTable = VALUESTablesReg.inverse().get(tableName);

      final UVar baseVar = mkFreshBaseVar();
      final List<Value> schemas = plan.valuesReg().valuesOf(nodeId);
      putTupleVarSchema(baseVar, schemas);
      push(visibleVars, baseVar);

      // Case 1. a table instance in database
      if (VALUESTable == null) return UTable.mk(UName.mk(tableName), baseVar);

      // Case 2. an enumerated table VALUES(tuple0, tuple1, ...)
      final List<UTerm> addFactors = new ArrayList<>();
      for (TupleInstance tuple : VALUESTable.tupleMultiSet.keySet()) {
        final List<UTerm> mulFactors = new ArrayList<>();
        assert tuple.size() == VALUESTable.schema.size();
        for (int i = 0, bound = VALUESTable.schema.size(); i < bound; ++i) {
          final UVar projVar = mkProjVar(schemas.get(i), baseVar);
          final Integer value = tuple.getValue(i);
          if (value == null) mulFactors.add(mkIsNullPred(UVarTerm.mk(projVar)));
          else mulFactors.add(UPred.mkBinary(EQ, UVarTerm.mk(projVar), UConst.mk(value)));
        }
        if (VALUESTable.tupleMultiSet.get(tuple) > 1)
          mulFactors.add(UConst.mk(VALUESTable.tupleMultiSet.get(tuple)));
        addFactors.add(UMul.mk(mulFactors));
      }

      if (addFactors.size() == 0) return UConst.zero();
      else return addFactors.size() == 1 ? addFactors.get(0) : UAdd.mk(addFactors);
    }

    private UTerm trFilter(int nodeId) {
      final UTerm predecessor = tr(plan.childOf(nodeId, 0));
      if (predecessor == null) return null;

      final SimpleFilterNode filter = (SimpleFilterNode) plan.nodeAt(nodeId);
      final Expression predExpr = filter.predicate();
      final UVar visibleVar = getVisibleVar();
      assert visibleVar != null;
      final UTerm pred = mkPredicate(predExpr, predExpr.template(), visibleVar);
      if (pred == null) return null;

      return UMul.mk(predecessor, pred);
    }

    private UTerm trInSubFilter(int nodeId) {
      final UTerm lhs = tr(plan.childOf(nodeId, 0));
      if (lhs == null) return null;

      final UVar lhsVisibleVar = tail(visibleVars);
      assert lhsVisibleVar != null;
      push(auxVars, lhsVisibleVar);
      final UTerm rhs = tr(plan.childOf(nodeId, 1));
      pop(auxVars);
      if (rhs == null) return null;

      // Store lhs visible var and free var only, rhs vars are no longer visible.
      final UVar rhsVisibleVar = pop(visibleVars);
      assert rhsVisibleVar != null;

      final InSubNode inSub = (InSubNode) plan.nodeAt(nodeId);
      final SqlNode lhsExpr = inSub.expr().template();
      final List<ComposedUTerm> lhsExprTerms = new ArrayList<>();
      if (Tuple.isInstance(lhsExpr)) {
        for (SqlNode e : lhsExpr.$(ExprFields.Tuple_Exprs)) {
          final ComposedUTerm term = mkValue(inSub.expr(), e, lhsVisibleVar);
          if (term == null) return null;
          lhsExprTerms.add(term);
        }
      } else {
        final ComposedUTerm term = mkValue(inSub.expr(), lhsExpr, lhsVisibleVar);
        if (term == null) return null;
        lhsExprTerms.add(term);
      }
      if (lhsExprTerms.isEmpty()) return null;

      final UTerm eqCond = mkInSubEqCond(lhsExprTerms, rhsVisibleVar);
      final UTerm decoratedRhs = USquash.mk(USum.mk(UVar.getBaseVars(rhsVisibleVar), UMul.mk(eqCond, rhs)));

      return UMul.mk(lhs, decoratedRhs);
    }

    private UTerm mkInSubEqCond(List<ComposedUTerm> lhsExprTerms, UVar rhsVar) {
      final List<Value> rhsVarSchema = getTupleVarSchema(rhsVar);
      assert lhsExprTerms.size() == rhsVarSchema.size();

      final List<UTerm> eqs = new ArrayList<>();
      for (int i = 0, bound = lhsExprTerms.size(); i < bound; ++i) {
        final ComposedUTerm lhsExprTerm = lhsExprTerms.get(i);
        final UVar rhsProjVar = mkProjVar(rhsVarSchema.get(i), rhsVar);
        final ComposedUTerm rhsProjVarComposedTerm = ComposedUTerm.mk(UVarTerm.mk(rhsProjVar));
        final UTerm eqCond = ComposedUTerm.doComparatorOp(lhsExprTerm, rhsProjVarComposedTerm, BinaryOpKind.EQUAL);
        eqs.add(eqCond);
      }
      assert !eqs.isEmpty();
      return eqs.size() == 1 ? eqs.get(0) : UMul.mk(eqs);
    }

    private UTerm trExistsFilter(int nodeId) {
      final UTerm lhs = tr(plan.childOf(nodeId, 0));
      if (lhs == null) return null;

      final UVar lhsVisibleVar = tail(visibleVars);
      assert lhsVisibleVar != null;
      push(auxVars, lhsVisibleVar);
      final UTerm rhs = tr(plan.childOf(nodeId, 1));
      pop(auxVars);
      if (rhs == null) return null;

      // Store lhs visible var and free var only, rhs vars are no longer visible.
      final UVar rhsVisibleVar = pop(visibleVars);
      assert rhsVisibleVar != null;
      final UTerm decoratedRhs = USquash.mk(USum.mk(UVar.getBaseVars(rhsVisibleVar), rhs));

      return UMul.mk(lhs, decoratedRhs);
    }

    private UVar generateOutVarSchema(UVar visibleVar, List<Value> outputValues) {
      UVar outVar;
      if (hasSameSourceColumns(outputValues)) {
        // Special case: there are output columns from the same source
        // should eliminate the ambiguity
        outVar = mkFreshVarFrom(visibleVar);
        if (outVar.is(UVar.VarKind.BASE))
          putTupleVarSchema(outVar, outputValues);
        else if (outVar.is(UVar.VarKind.CONCAT))
          outVar = putConcatVarSchema(outVar, visibleVar, outputValues);
        else assert false;
      } else {
        // Common case
        outVar = mkFreshBaseVar();
        putTupleVarSchema(outVar, outputValues);
      }
      push(visibleVars, outVar);
      return outVar;
    }

    private UTerm trProj(int nodeId) {
      final UTerm predecessor = tr(plan.childOf(nodeId, 0));
      if (predecessor == null) return null;

      /*
       * Generate the output var and schema
       */

      final ProjNode proj = (ProjNode) plan.nodeAt(nodeId);
      final UVar visibleVar = pop(visibleVars);
      assert visibleVar != null;

      final List<Value> outputValues = plan.valuesReg().valuesOf(nodeId);
      UVar outVar = generateOutVarSchema(visibleVar, outputValues);

      /*
       * Generate the summation body
       */

      final UTerm eqCond = mkProjEqCond(outputValues, proj.attrExprs(), outVar, visibleVar);
      if (eqCond == null) return null;

      // Case 1. Common summation introduced by Proj, since input expr is not from VALUES table
      if (all(UVar.getBaseVars(visibleVar), v -> cannotEnumerateProjSummation(predecessor, v))) {
        UTerm summation = USum.mk(UVar.getBaseVars(visibleVar), UMul.mk(eqCond, predecessor));
        if (isSingleValueProj(proj.attrExprs())) {
          final UTerm firstPred = UPred.mkBinary(EQ, (proj.deduplicated() ? USquash.mk(summation) : summation), UConst.one());
          final UTerm secondPred = UPred.mkBinary(EQ, USum.mk(UVar.getBaseVars(visibleVar), predecessor.copy()), UConst.one());
          return UMul.mk(firstPred, secondPred);
        }
        return proj.deduplicated() ? USquash.mk(summation) : summation;
      }

      // Case 2. Input expr is from VALUES table: build a template to expand summation with finite tuples
      final UTerm normalizedPredecessor = UExprSupport.normalizeExpr(predecessor);
      final UTerm template = UMul.mk(eqCond, normalizedPredecessor);
      // TODO: visibleVar is CONCAT var
      final Set<TupleInstance> tupleInstances = searchTupleInstances(normalizedPredecessor, visibleVar);
      final List<UTerm> instantiatedTerms = new ArrayList<>();
      for (TupleInstance tupleInstance : tupleInstances) {
        UTerm instantiation = template.copy();
        for (var pair : zip(getTupleVarSchema(visibleVar), tupleInstance.values())) {
          final Value schemaAttr = pair.getLeft();
          final Integer val = pair.getRight();
          final UVarTerm projVarTerm = UVarTerm.mk(mkProjVar(schemaAttr, visibleVar));
          if (val != null) instantiation = instantiation.replaceAtomicTerm(projVarTerm, UConst.mk(val));
          else instantiation = propagateNullVar(instantiation, projVarTerm); // Null value of tuple
        }
        instantiatedTerms.add(instantiation);
      }

      UTerm res;
      if (instantiatedTerms.size() == 0) {
        if(usingUString(template)) {
          res = USum.mk(UVar.getBaseVars(visibleVar),template).copy();
          return proj.deduplicated() ? USquash.mk(res) : res;
        }
        res = UConst.zero();
      }
      else res = instantiatedTerms.size() == 1 ? instantiatedTerms.get(0) : UAdd.mk(instantiatedTerms);

      return proj.deduplicated() ? USquash.mk(res) : res;
    }

    private boolean cannotEnumerateProjSummation(UTerm expr, UVar baseVar) {
      if (expr.kind() == TABLE && expr.isUsing(baseVar)) return true;
      if (expr.kind() == SUMMATION) return true;

      return any(expr.subTerms(), t -> cannotEnumerateProjSummation(t, baseVar));
    }

    private boolean usingUString(UTerm expr) {
      if(expr.kind() == STRING) return true;
      List<UTerm> subTerms = expr.subTerms();
      for(UTerm subTerm : subTerms) {
        if(usingUString(subTerm))
          return true;
      }
      return false;
    }

    private Set<TupleInstance> searchTupleInstances(UTerm expr, UVar baseVar) {
      final Set<TupleInstance> tupleInstances = new HashSet<>();
      for (UTerm subTerm : expr.subTerms())
        tupleInstances.addAll(searchTupleInstances(subTerm, baseVar));

      if (expr.kind() != MULTIPLY && expr.kind() != PRED) return tupleInstances;

      assert baseVar.is(UVar.VarKind.BASE);
      final List<Value> tupleSchema = getTupleVarSchema(baseVar);
      final List<UTerm> predicates = expr.kind() == MULTIPLY ? expr.subTermsOfKind(PRED) : List.of(expr);
      final List<Integer> tupleValues = new ArrayList<>();
      for (Value value : tupleSchema) {
        boolean match = false;
        final UVarTerm targetProjVar = UVarTerm.mk(mkProjVar(value, baseVar));
        for (UTerm subTerm : predicates) {
          final UPred pred = (UPred) subTerm;
          if (pred.isPredKind(EQ)) {
            assert pred.args().size() == 2;
            final UTerm arg0 = pred.args().get(0), arg1 = pred.args().get(1);
            if ((arg0.equals(targetProjVar) && arg1.kind() == CONST) ||
                (arg1.equals(targetProjVar) && arg0.kind() == CONST)) {
              final UConst constVal = (UConst) (arg1.kind() == CONST ? arg1 : arg0);
              tupleValues.add(constVal.value());
              match = true;
              break;
            }
          } else if (varIsNullPred(pred) && getIsNullPredVar(pred).equals(targetProjVar.var())) {
            tupleValues.add(null);
            match = true;
            break;
          }
        }
        if (!match) return tupleInstances;
      }
      assert tupleValues.size() == tupleSchema.size();
      tupleInstances.add(TupleInstance.mk(tupleValues));

      return tupleInstances;
    }

    private Set<TupleInstanceStr> searchTupleInstancesStr(UTerm expr, UVar baseVar) {
      final Set<TupleInstanceStr> tupleInstances = new HashSet<>();
      for (UTerm subTerm : expr.subTerms())
        tupleInstances.addAll(searchTupleInstancesStr(subTerm, baseVar));

      if (expr.kind() != MULTIPLY && expr.kind() != PRED) return tupleInstances;

      assert baseVar.is(UVar.VarKind.BASE);
      final List<Value> tupleSchema = getTupleVarSchema(baseVar);
      final List<UTerm> predicates = expr.kind() == MULTIPLY ? expr.subTermsOfKind(PRED) : List.of(expr);
      final List<String> tupleValues = new ArrayList<>();
      for (Value value : tupleSchema) {
        boolean match = false;
        final UVarTerm targetProjVar = UVarTerm.mk(mkProjVar(value, baseVar));
        for (UTerm subTerm : predicates) {
          final UPred pred = (UPred) subTerm;
          if (pred.isPredKind(EQ)) {
            assert pred.args().size() == 2;
            final UTerm arg0 = pred.args().get(0), arg1 = pred.args().get(1);
            if ((arg0.equals(targetProjVar) && arg1.kind() == STRING) ||
                    (arg1.equals(targetProjVar) && arg0.kind() == STRING)) {
              final UString stringVal = (UString) (arg1.kind() == STRING ? arg1 : arg0);
              tupleValues.add(stringVal.value());
              match = true;
              break;
            }
          } else if (varIsNullPred(pred) && getIsNullPredVar(pred).equals(targetProjVar.var())) {
            tupleValues.add(null);
            match = true;
            break;
          }
        }
        if (!match) return tupleInstances;
      }
      assert tupleValues.size() == tupleSchema.size();
      TupleInstanceStr instanceStr = TupleInstanceStr.mk(tupleValues);
      if(!tupleInstances.contains(instanceStr)) {
        tupleInstances.add(TupleInstanceStr.mk(tupleValues));
      }
      return tupleInstances;
    }

    private UTerm propagateNullVar(UTerm expr, UVarTerm nullVarTerm) {
      expr = transformSubTerms(expr, e -> propagateNullVar(e, nullVarTerm));
      if (expr.kind() != PRED) return expr;

      final UPred pred = (UPred) expr;
      if (varIsNullPred(pred) && getIsNullPredVar(pred).equals(nullVarTerm.var())) return UConst.one();
      if (pred.isPredKind(EQ)) {
        final UTerm arg0 = pred.args().get(0), arg1 = pred.args().get(1);
        if (!arg0.equals(nullVarTerm) && !arg1.equals(nullVarTerm)) return expr;
        final UTerm targetVarTerm = arg0.equals(nullVarTerm) ? arg0 : arg1;
        final UTerm otherTerm = targetVarTerm == arg0 ? arg1 : arg0;
        if (otherTerm.kind() == CONST) return UConst.zero();
        else if (otherTerm.kind() == VAR) return mkIsNullPred((UVarTerm) otherTerm);
      }

      return expr;
    }

    private boolean isSingleValueProj(List<Expression> projList) {
      if(projList.get(0).template().$(ExprFields.FuncCall_Name) != null) {
        return Objects.equals(projList.get(0).template().$(ExprFields.FuncCall_Name).toString(), "`single_value`");
      }
      return false;
    }

    boolean projListEqNull(SqlNode node) {
      final ExprKind exprKind = node.$(Expr_Kind);
      if(exprKind == Binary) {
        final BinaryOpKind binaryOpKind = node.$(ExprFields.Binary_Op);
        if(binaryOpKind == EQUAL) {
          final SqlNode leftNode = node.$(ExprFields.Binary_Left);
          final SqlNode rightNode = node.$(ExprFields.Binary_Right);
          return (leftNode.$(Expr_Kind) == Literal && leftNode.$(ExprFields.Literal_Kind) == NULL && rightNode.$(Expr_Kind) != Literal)
                  || (rightNode.$(Expr_Kind) == Literal && rightNode.$(ExprFields.Literal_Kind) == NULL && leftNode.$(Expr_Kind) != Literal);
        }
      }
      return false;
    }

    private UTerm mkProjEqCond(List<Value> outputs, List<Expression> projList, UVar outVar, UVar inVar) {
      assert outputs.size() == projList.size();

      final List<UTerm> eqs = new ArrayList<>();
      for (int i = 0, bound = outputs.size(); i < bound; ++i) {
        final UVar outProjVar = mkProjVar(outputs.get(i), outVar);
        final ComposedUTerm projTargetTerm = mkValue(projList.get(i), projList.get(i).template(), inVar);
        if (projListEqNull(projList.get(i).template())) {
          final UTerm freeProjTerm = mkIsNullPred(outProjVar);
          eqs.add(freeProjTerm);
          continue;
        }
        if (projTargetTerm == null) return null;
        if (projTargetTerm.getSubQueryOutVar() != null) {
          projTargetTerm.replaceVar(projTargetTerm.getSubQueryOutVar(), outProjVar);
          final UTerm freeProjTerm = projTargetTerm.toPredUTerm();
          eqs.add(freeProjTerm);
          continue;
        }
        final ComposedUTerm outProjVarTerm = ComposedUTerm.mk(UVarTerm.mk(outProjVar));
        final UTerm freeProjTerm = ComposedUTerm.doComparatorOp(outProjVarTerm, projTargetTerm, BinaryOpKind.IS);
        eqs.add(freeProjTerm);
      }
      return UMul.mk(eqs);
    }

    private UTerm trJoin(int nodeId) {
      final UTerm lhs = tr(plan.childOf(nodeId, 0));
      final UTerm rhs = tr(plan.childOf(nodeId, 1));
      if (lhs == null || rhs == null) return null;

      final JoinNode join = (JoinNode) plan.nodeAt(nodeId);
      final JoinKind joinKind = join.joinKind();
      final UVar rhsVisibleVar = pop(visibleVars);
      final UVar lhsVisibleVar = pop(visibleVars);
      assert rhsVisibleVar != null && lhsVisibleVar != null;

      final UVar outVisibleVar = UVar.mkConcat(lhsVisibleVar, rhsVisibleVar);
      push(visibleVars, outVisibleVar);

      if (joinKind == JoinKind.CROSS_JOIN) return UMul.mk(lhs, rhs);

      final Expression joinCond = join.joinCond();
      UTerm joinCondTerm = null;
      if (joinCond != null) {
        joinCondTerm = mkPredicate(joinCond, joinCond.template(), outVisibleVar);
      } else {
        ArrayList<UTerm> args = new ArrayList<>();
        args.add(UConst.one());
        args.add(UConst.one());
        joinCondTerm = UPred.mk(EQ, UName.mk("="), args);
      }
      if (joinCondTerm == null) return null;

      final UTerm innerJoinBody = UMul.mk(lhs, rhs, joinCondTerm);
      if (joinKind == JoinKind.INNER_JOIN) return innerJoinBody;

      // Left Join
      if (joinKind == JoinKind.LEFT_JOIN) {
        UTerm newSum = USum.mk(UVar.getBaseVars(rhsVisibleVar), UMul.mk(rhs, joinCondTerm).copy());
        newSum = replaceAllBoundedVars(newSum);
        UTerm specificScalarTerm = null;
        // left join on scalar query and condition is true
        if((specificScalarTerm = getLeftJoinScalarQueryTerm(plan.childOf(nodeId, 1))) != null && joinCondTerm.equals(UConst.one())) {
          // not([summation = 1] + [summation > 1])
          final UMul lJoinBody = UMul.mk(lhs.copy(), mkIsNullPredForAllAttrs(rhsVisibleVar),
                  UNeg.mk(UAdd.mk(UPred.mkBinary(EQ, specificScalarTerm.copy(), UConst.one()), UPred.mkBinary(GT, specificScalarTerm.copy(), UConst.one()))));
          return UAdd.mk(innerJoinBody, lJoinBody);
        }
        final UMul lJoinBody = UMul.mk(lhs.copy(), mkIsNullPredForAllAttrs(rhsVisibleVar), UNeg.mk(newSum));
        return UAdd.mk(innerJoinBody, lJoinBody);
      }
      // Right Join
      if (joinKind == JoinKind.RIGHT_JOIN) {
        UTerm newSum = USum.mk(UVar.getBaseVars(lhsVisibleVar), UMul.mk(lhs, joinCondTerm).copy());
        newSum = replaceAllBoundedVars(newSum);
        final UMul rJoinBody = UMul.mk(rhs.copy(), mkIsNullPredForAllAttrs(lhsVisibleVar), UNeg.mk(newSum));
        return UAdd.mk(innerJoinBody, rJoinBody);
      }
      // Full Join
      if (joinKind == JoinKind.FULL_JOIN) {
        UTerm newSumLJoin = USum.mk(UVar.getBaseVars(rhsVisibleVar), UMul.mk(rhs, joinCondTerm).copy());
        newSumLJoin = replaceAllBoundedVars(newSumLJoin);
        final UTerm lJoinBody = UMul.mk(lhs.copy(), mkIsNullPredForAllAttrs(rhsVisibleVar), UNeg.mk(newSumLJoin));

        UTerm newSumRJoin = USum.mk(UVar.getBaseVars(lhsVisibleVar), UMul.mk(lhs, joinCondTerm).copy());
        newSumRJoin = replaceAllBoundedVars(newSumRJoin);
        final UTerm rJoinBody = UMul.mk(rhs.copy(), mkIsNullPredForAllAttrs(lhsVisibleVar), UNeg.mk(newSumRJoin));

        return UAdd.mk(innerJoinBody, lJoinBody, rJoinBody);
      }

      throw new IllegalArgumentException("Unsupported join type" + joinKind);
    }

    private UTerm mkIsNullPredForAllAttrs(UVar base) {
      final List<Value> schema = getTupleVarSchema(base);
      final List<UTerm> subTerms = new ArrayList<>();
      for (Value v : schema) {
        final UVar projVar = mkProjVar(v, base);
        subTerms.add(mkIsNullPred(UVarTerm.mk(projVar)));
      }
      assert !subTerms.isEmpty();
      return subTerms.size() == 1 ? subTerms.get(0) : UMul.mk(subTerms);
    }

    private UTerm trSetOp(int nodeId) {
      final UTerm lhs = tr(plan.childOf(nodeId, 0));
      final UTerm rhs = tr(plan.childOf(nodeId, 1));
      if (lhs == null || rhs == null) return null;

      final SetOpNode setOpNode = (SetOpNode) plan.nodeAt(nodeId);
      final UVar rhsVisibleVar = pop(visibleVars);
      final UVar lhsVisibleVar = pop(visibleVars);
      assert rhsVisibleVar != null && lhsVisibleVar != null;
      assert lhsVisibleVar.kind() == rhsVisibleVar.kind()
          && lhsVisibleVar.args().length == rhsVisibleVar.args().length
          : "different visible var types of Union's children";

      final List<Value> lhsSchema = getTupleVarSchema(lhsVisibleVar);
      final List<Value> rhsSchema = getTupleVarSchema(rhsVisibleVar);
      assert lhsSchema.size() == rhsSchema.size() : "Schemas of Union's children are not aligned";
      // Replace each projVar in rhs with corresponding projVar of lhs
      // Make lhs visible var to be output visible var
      for (var schemaPair : zip(lhsSchema, rhsSchema)) {
        final UVar lhsProjVar = mkProjVar(schemaPair.getLeft(), lhsVisibleVar);
        final UVar rhsProjVar = mkProjVar(schemaPair.getRight(), rhsVisibleVar);
        rhs.replaceVarInplace(rhsProjVar, lhsProjVar, false);
      }
      for (int i = 0, bound = lhsVisibleVar.args().length; i < bound; i++) {
        rhs.replaceVarInplace(rhsVisibleVar.args()[i], lhsVisibleVar.args()[i], false);
      }
      push(visibleVars, lhsVisibleVar);

      switch (setOpNode.opKind()) {
        case UNION -> {
          UTerm union = UAdd.mk(lhs, rhs);
          if (setOpNode.deduplicated()) union = USquash.mk(union);
          return union;
        }
        case INTERSECT -> {
          if (setOpNode.deduplicated()) return USquash.mk(UMul.mk(lhs, rhs));
          else return UAdd.mk(UMul.mk(lhs, USquash.mk(rhs)), UMul.mk(USquash.mk(lhs.copy()), rhs.copy()));
        }
        case EXCEPT -> {
          UTerm except = UMul.mk(lhs, UNeg.mk(rhs));
          if (setOpNode.deduplicated()) except = USquash.mk(except);
          return except;
        }
        default -> throw new IllegalArgumentException("unknown set operator" + setOpNode);
      }
    }

    private boolean isPredLiteralFalse(int nodeId) {
      if(plan.kindOf(nodeId)!=PlanKind.Filter) return false;
      final SimpleFilterNode filter = (SimpleFilterNode) plan.nodeAt(nodeId);
      final Expression predExpr = filter.predicate();
      final SqlNode node = predExpr.template();
      if(node.$(Expr_Kind) != Literal) return false;
      if(node.$(ExprFields.Literal_Kind) != BOOL) return false;
      final Boolean value = (Boolean) node.$(ExprFields.Literal_Value);
      return value == Boolean.FALSE;
    }

    private UTerm trAgg(int nodeId) {
      final UTerm predecessor = tr(plan.childOf(plan.childOf(nodeId, 0), 0));
      if (predecessor == null) return null;

      final AggNode agg = (AggNode) plan.nodeAt(nodeId);
      final UVar visibleVar = pop(visibleVars);
      assert visibleVar != null;

      final List<Value> outputValues = plan.valuesReg().valuesOf(nodeId);
      final UVar outVar = generateOutVarSchema(visibleVar, outputValues);

      final List<Expression> aggregateExprs = new ArrayList<>(3);
      final List<Value> aggregateOutputs = new ArrayList<>(3);
      final List<Expression> commonProjExprs = new ArrayList<>(3);
      final List<Value> commonProjOutputs = new ArrayList<>(3);
      if(isExceptionAgg(agg))
        return null;
      collectExprsOnAgg(agg, aggregateExprs, aggregateOutputs, commonProjExprs, commonProjOutputs);

      /*
       * TODO:  add an extra Proj if:
       *  1. groupBy lists is different from select list
       *  2. If `HAVING count(*) > 1` but `count(*)` does not exists in select list
       */


      final List<UTerm> subTerms = new ArrayList<>(3);
      // Part1: Eq-conditions for common projected columns in select list
      final UTerm commonProjBody = commonProjExprs.isEmpty() ?
          predecessor :
          UMul.mk(predecessor, mkProjEqCond(commonProjOutputs, commonProjExprs, outVar, visibleVar));
      if (!commonProjExprs.isEmpty()) {
        final UTerm commonProjTerm = USquash.mk(USum.mk(UVar.getBaseVars(visibleVar), commonProjBody));
        subTerms.add(commonProjTerm);
      }

      // Part2: Eq-conditions for Aggregated result in select list
      if (!aggregateExprs.isEmpty()) {
        final UTerm aggregateTerm =
            mkAggOutVarEqCond(aggregateOutputs, aggregateExprs, outVar, visibleVar, commonProjBody.copy(),
                    commonProjExprs.isEmpty() && isPredLiteralFalse(plan.childOf(plan.childOf(nodeId, 0), 0)));
        if (aggregateTerm == null) return null;
        subTerms.add(aggregateTerm);
      }

      // Part3: HAVING predicate
      if (agg.havingExpr() != null) {
        UTerm havingPred = null;
        for (int i = 0, bound = agg.attrExprs().size(); i < bound; ++i) {
          if (agg.havingExpr().toString().equals(agg.attrExprs().get(i).toString())) {
            final UVar havingPredProjVar = mkProjVar(outputValues.get(i), outVar);
            havingPred = mkPredicate(agg.havingExpr(), agg.havingExpr().template(), outVar);
          }
        }
        if (havingPred != null) {
          subTerms.add(havingPred);
        }
      }
      return UMul.mk(subTerms);
    }

    private UTerm trLimit(int nodeId) {
      final UTerm predecessor = tr(plan.childOf(nodeId, 0));
      if (predecessor == null) return null;
      if(isZeroLimit(nodeId)) {
        return UConst.zero();
      }
      throw new IllegalArgumentException("Unsupported Limit Case");
    }

    private UTerm trSort(int nodeId) {
      final UTerm predecessor = tr(plan.childOf(nodeId, 0));
      if (predecessor == null) return null;
      if(isZeroLimit(plan.parentOf(nodeId)) || isOneLimit(plan.parentOf(nodeId)))
        return predecessor;
      throw new IllegalArgumentException("Unsupported Sort Case");
    }

    boolean isZeroLimit(int nodeId) {
      if(plan.kindOf(nodeId) != PlanKind.Limit) return false;
      final SqlNode limit = ((LimitNode) plan.nodeAt(nodeId)).limit().template();
      return Literal.isInstance(limit) && limit.$(ExprFields.Literal_Value) == (Integer) 0;
    }

    boolean isOneLimit(int nodeId) {
      if(plan.kindOf(nodeId) != PlanKind.Limit) return false;
      final SqlNode limit = ((LimitNode) plan.nodeAt(nodeId)).limit().template();
      return Literal.isInstance(limit) && limit.$(ExprFields.Literal_Value) == (Integer) 1;
    }

    // select list column should also exist in group by
    private boolean isExceptionAgg(AggNode agg) {
      List<String> groupByColRefs = new ArrayList<>();
      List<String> selectListColRefs = new ArrayList<>();
      for(Expression groupByExpr : agg.groupByExprs()) {
        for(SqlNode colRef : groupByExpr.colRefs()) {
          if(colRef.$(ExprFields.ColRef_ColName) != null) {
            assert(colRef.$(ExprFields.ColRef_ColName).kind() == SqlKind.ColName);
            groupByColRefs.add(colRef.$(ExprFields.ColRef_ColName).$(ColName_Col));
          }
        }
      }
      for(Expression attrExpr : agg.attrExprs()) {
        if(!isAggregateExpression(attrExpr))
          for(SqlNode colRef : attrExpr.colRefs()) {
            if(colRef.$(ExprFields.ColRef_ColName) != null) {
              assert(colRef.$(ExprFields.ColRef_ColName).kind() == SqlKind.ColName);
              selectListColRefs.add(colRef.$(ExprFields.ColRef_ColName).$(ColName_Col));
            }
          }
      }
      for(String selectListColRef : selectListColRefs) {
          if(!groupByColRefs.contains(selectListColRef)) {
            if(isTargetSide)
              System.err.println("Select list not in Group list target");
            else
              System.err.println("Select list not in Group list source");
            return true;
          }
      }
//      for(String groupByColRef : groupByColRefs) {
//        if(!selectListColRefs.contains(groupByColRef))
//          return true;
//      }

      return false;
    }

    private void collectExprsOnAgg(
        AggNode agg,
        List<Expression> aggregateExprs,
        List<Value> aggregateOutputs,
        List<Expression> groupByExprs,
        List<Value> groupByOutputs) {
      final List<Expression> attrExprs = agg.attrExprs();
      final List<Value> outputValues = plan.valuesReg().valuesOf(plan.nodeIdOf(agg));
      for (int i = 0, bound = attrExprs.size(); i < bound; ++i) {
        final Expression attrExpr = attrExprs.get(i);
        if (isAggregateExpression(attrExpr)) {
          aggregateExprs.add(attrExpr);
          aggregateOutputs.add(outputValues.get(i));
        } else {
          groupByExprs.add(attrExpr);
          groupByOutputs.add(outputValues.get(i));
        }
      }
    }

    private UTerm mkAggOutVarEqCond(
        List<Value> outputs,
        List<Expression> aggList,
        UVar outVar,
        UVar inVar,
        UTerm groupByTerm,
        boolean isNullReturn) {
      assert outputs.size() == aggList.size();

      final List<UTerm> subTerms = new ArrayList<>();
      for (int i = 0, bound = outputs.size(); i < bound; ++i) {
        final Value value = outputs.get(i);
        final Expression aggExpr = aggList.get(i);

        final UVar outProjVar = mkProjVar(value, outVar);
        List<Value> aggValueRefs = plan.valuesReg().valueRefsOf(aggExpr);
        boolean isCountStar = false;
        if (aggExpr.template().$(ExprFields.Aggregate_Args) == null)
          isCountStar = false;
        else
          isCountStar = Wildcard.isInstance(aggExpr.template().$(ExprFields.Aggregate_Args).get(0));
        if (isCountStar)
          aggValueRefs = getTupleVarSchema(inVar); // Special case for `count(*)`

        final List<UVar> aggProjVars = map(aggValueRefs, v -> mkProjVar(v, inVar));

        final String aggFunc = getAggregateFunction(aggExpr);
        if (aggFunc == null) return null;
        UTerm aggTerm;
        switch (aggFunc.toLowerCase()) {
          case "count" -> {
            final Boolean dedupFlag = aggExpr.template().$(ExprFields.Aggregate_Distinct);
            if (dedupFlag != null && dedupFlag) {
              final UVar newBaseVar = mkFreshBaseVar();
              putTupleVarSchema(newBaseVar, aggValueRefs);
              final List<UVar> newProjVars = map(aggValueRefs, v -> mkProjVar(v, newBaseVar));
              final List<UTerm> innerEqPredList =
                  map(
                      zip(aggProjVars, newProjVars),
                      pair -> UPred.mkBinary(EQ, pair.getLeft(), pair.getRight()));
              final UTerm innerEqs = UMul.mk(innerEqPredList);
              final UTerm innerNotNulls = UMul.mk(map(aggProjVars, UExprSupport::mkNotNullPred));
              final UTerm innerSummationBody = UMul.mk(groupByTerm, innerEqs, innerNotNulls);
              final UTerm innerSummation = USum.mk(UVar.getBaseVars(inVar), innerSummationBody);
              final UTerm outerSummation = USum.mk(UVar.getBaseVars(newBaseVar), USquash.mk(innerSummation));
              aggTerm = UPred.mkBinary(EQ, UVarTerm.mk(outProjVar), outerSummation);
            } else if(!isCountStar) {
              final UTerm notNulls = UMul.mk(map(aggProjVars, UExprSupport::mkNotNullPred));
              final UTerm countSummation = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm, notNulls));
              aggTerm = UPred.mkBinary(EQ, UVarTerm.mk(outProjVar), countSummation);
            } else {
              final UTerm countSummation = USum.mk(UVar.getBaseVars(inVar), groupByTerm);
              aggTerm = UPred.mkBinary(EQ, UVarTerm.mk(outProjVar), countSummation);
            }
          }
          case "sum" -> {
            assert aggProjVars.size() == 1;
            final Boolean dedupFlag = aggExpr.template().$(ExprFields.Aggregate_Distinct);
            if (dedupFlag != null && dedupFlag) {
              assert aggValueRefs.size() == 1;
              final UVar newBaseVar = mkFreshBaseVar();
              putTupleVarSchema(newBaseVar, aggValueRefs);
              final UVar newProjVar = mkProjVar(aggValueRefs.get(0), newBaseVar);
              final UTerm innerEqPred = UPred.mkBinary(EQ, aggProjVars.get(0), newProjVar);
              final UTerm innerEqs = UMul.mk(innerEqPred);
              final UTerm innerSummationBody = UMul.mk(groupByTerm, innerEqs);
              final UTerm innerSummation = USum.mk(UVar.getBaseVars(inVar), innerSummationBody);
              final UTerm outerNotNull = UMul.mk(mkNotNullPred(newProjVar));
              final UTerm outerMultiplyBody = UMul.mk(UVarTerm.mk(newProjVar), outerNotNull, USquash.mk(innerSummation));
              final UTerm outerSummation = USum.mk(UVar.getBaseVars(newBaseVar), outerMultiplyBody);
              aggTerm = UPred.mkBinary(EQ, UVarTerm.mk(outProjVar), outerSummation);
            } else {
              final UTerm sumProjVar = UVarTerm.mk(aggProjVars.get(0));
              final UTerm notNull = mkNotNullPred(aggProjVars.get(0));
              final UTerm sumSummation = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm, notNull, sumProjVar));
              aggTerm = UPred.mkBinary(EQ, UVarTerm.mk(outProjVar), sumSummation);
            }
            if(isNullReturn) aggTerm = mkIsNullPred(UVarTerm.mk(outProjVar));
          }
          case "avg", "average" -> {
            assert aggProjVars.size() == 1;
            final Boolean dedupFlag = aggExpr.template().$(ExprFields.Aggregate_Distinct);
            if(dedupFlag != null && dedupFlag) {
              assert aggValueRefs.size() == 1;
              // COUNT DISTINCT
              final UVar newBaseVar = mkFreshBaseVar();
              putTupleVarSchema(newBaseVar, aggValueRefs);
              final List<UVar> newCountProjVars = map(aggValueRefs, v -> mkProjVar(v, newBaseVar));
              final List<UTerm> innerEqPredList =
                  map(
                      zip(aggProjVars, newCountProjVars),
                      pair -> UPred.mkBinary(EQ, pair.getLeft(), pair.getRight()));
              final UTerm innerCountEqs = UMul.mk(innerEqPredList);
              final UTerm innerCountNotNulls = UMul.mk(map(aggProjVars, UExprSupport::mkNotNullPred));
              final UTerm innerCountSummationBody = UMul.mk(groupByTerm, innerCountEqs, innerCountNotNulls);
              final UTerm innerCountSummation = USum.mk(UVar.getBaseVars(inVar), innerCountSummationBody);
              final UTerm outerCountSummation = USum.mk(UVar.getBaseVars(newBaseVar), USquash.mk(innerCountSummation));

              // SUM DISTINCT
              final UVar newSumBaseVar = mkFreshBaseVar();
              putTupleVarSchema(newSumBaseVar, aggValueRefs);
              final UVar newProjVar = mkProjVar(aggValueRefs.get(0), newSumBaseVar);
              final UTerm innerSumEqPred = UPred.mkBinary(EQ, aggProjVars.get(0), newProjVar);
              final UTerm innerSumEqs = UMul.mk(innerSumEqPred);
              final UTerm innerSumSummationBody = UMul.mk(groupByTerm, innerSumEqs);
              final UTerm innerSumSummation = USum.mk(UVar.getBaseVars(inVar), innerSumSummationBody);
              final UTerm outerSumNotNull = UMul.mk(mkNotNullPred(newProjVar));
              final UTerm outerSumMultiplyBody = UMul.mk(UVarTerm.mk(newProjVar), outerSumNotNull, USquash.mk(innerSumSummation));
              final UTerm outerSumSummation = USum.mk(UVar.getBaseVars(newSumBaseVar), outerSumMultiplyBody);

              aggTerm =
                  UPred.mkBinary(
                      EQ, UMul.mk(UVarTerm.mk(outProjVar), outerCountSummation), outerSumSummation);
            } else {
              final UTerm avgProjVar = UVarTerm.mk(aggProjVars.get(0));
              final UTerm notNull = mkNotNullPred(aggProjVars.get(0));
              final UTerm sumSummation = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm, notNull, avgProjVar));
              final UTerm countSummation = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm.copy(), notNull.copy()));
              aggTerm =
                  UPred.mkBinary(
                      EQ, UMul.mk(UVarTerm.mk(outProjVar), countSummation), sumSummation);
            }
            if(isNullReturn) aggTerm = mkIsNullPred(UVarTerm.mk(outProjVar));
          }
          case "max", "min" -> {
            assert aggProjVars.size() == 1;
            final UVar maxminProjVar = aggProjVars.get(0);
            final UPred.PredKind predKind = "max".equalsIgnoreCase(aggFunc) ? UPred.PredKind.GT : UPred.PredKind.LT;
            final UTerm notSumPred = UPred.mkBinary(predKind, maxminProjVar, outProjVar);
            final UTerm notSum = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm, notSumPred));
            final UTerm squashSumPred = UPred.mkBinary(EQ, maxminProjVar, outProjVar);
            final UTerm squashSum = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm.copy(), squashSumPred));
            aggTerm = UMul.mk(UNeg.mk(notSum), USquash.mk(squashSum));
            if(isNullReturn) aggTerm = mkIsNullPred(UVarTerm.mk(outProjVar));
          }
          case "var_pop" -> {
            assert aggProjVars.size() == 1;
            UTerm cnt = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm.copy(), mkNotNullPred(aggProjVars.get(0))));
            UTerm sum1 = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm.copy(), UVarTerm.mk(aggProjVars.get(0)),
                    UVarTerm.mk(aggProjVars.get(0)),mkNotNullPred(aggProjVars.get(0))));
            UTerm sum2 = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm.copy(), UVarTerm.mk(aggProjVars.get(0)),
                    mkNotNullPred(aggProjVars.get(0))));
            UTerm rightTerm = UMul.mk(cnt.copy(), sum1.copy());
            UTerm leftFirstTerm = UMul.mk(UVarTerm.mk(outProjVar), cnt.copy(), cnt.copy());
            UTerm leftSecondTerm = UMul.mk(sum2.copy(), sum2.copy());
            aggTerm = UPred.mk(EQ, UName.mk("="), List.of(UAdd.mk(leftFirstTerm, leftSecondTerm), rightTerm));
          }
          case "var_sample", "var_samp" -> {
            assert aggProjVars.size() == 1;
            UTerm cnt = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm.copy(), mkNotNullPred(aggProjVars.get(0))));
            UTerm sum1 = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm.copy(), UVarTerm.mk(aggProjVars.get(0)),
                    UVarTerm.mk(aggProjVars.get(0)),mkNotNullPred(aggProjVars.get(0))));
            UTerm sum2 = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm.copy(), UVarTerm.mk(aggProjVars.get(0)),
                    mkNotNullPred(aggProjVars.get(0))));
            UTerm rightTerm = UMul.mk(cnt.copy(), sum1.copy());
            UTerm leftFirstTerm = UMul.mk(UVarTerm.mk(outProjVar), cnt.copy(), UAdd.mk(cnt.copy(), UConst.mk(-1)));
            UTerm leftSecondTerm = UMul.mk(sum2.copy(), sum2.copy());
            UTerm equalPred = UPred.mk(EQ, UName.mk("="), List.of(UAdd.mk(leftFirstTerm, leftSecondTerm), rightTerm));
            UTerm cntGreatPred = UPred.mk(GT, UName.mk(">"), List.of(cnt.copy(), UConst.one()));
            UTerm cntEqualPred = UPred.mk(EQ, UName.mk("="), List.of(cnt.copy(), UConst.one()));
            UTerm isNullPred = mkIsNullPred(outProjVar);
            aggTerm = UAdd.mk(UMul.mk(cntGreatPred, equalPred), UMul.mk(cntEqualPred, isNullPred));
          }
          case "stddev_pop" -> {
            assert aggProjVars.size() == 1;
            UTerm cnt = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm.copy(), mkNotNullPred(aggProjVars.get(0))));
            UTerm sum1 = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm.copy(), UVarTerm.mk(aggProjVars.get(0)),
                                   UVarTerm.mk(aggProjVars.get(0)),mkNotNullPred(aggProjVars.get(0))));
            UTerm sum2 = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm.copy(), UVarTerm.mk(aggProjVars.get(0)),
                                   mkNotNullPred(aggProjVars.get(0))));
            UTerm rightTerm = UMul.mk(cnt.copy(), sum1.copy());
            UTerm leftFirstTerm = UMul.mk(UVarTerm.mk(outProjVar), UVarTerm.mk(outProjVar), cnt.copy(), cnt.copy());
            UTerm leftSecondTerm = UMul.mk(sum2.copy(), sum2.copy());
            aggTerm = UPred.mk(EQ, UName.mk("="), List.of(UAdd.mk(leftFirstTerm, leftSecondTerm), rightTerm));
          }
          case "stddev_sample", "stddev_samp" -> {
            assert aggProjVars.size() == 1;
            UTerm cnt = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm.copy(), mkNotNullPred(aggProjVars.get(0))));
            UTerm sum1 = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm.copy(), UVarTerm.mk(aggProjVars.get(0)),
                    UVarTerm.mk(aggProjVars.get(0)),mkNotNullPred(aggProjVars.get(0))));
            UTerm sum2 = USum.mk(UVar.getBaseVars(inVar), UMul.mk(groupByTerm.copy(), UVarTerm.mk(aggProjVars.get(0)),
                    mkNotNullPred(aggProjVars.get(0))));
            UTerm rightTerm = UMul.mk(cnt.copy(), sum1.copy());
            UTerm leftFirstTerm = UMul.mk(UVarTerm.mk(outProjVar), UVarTerm.mk(outProjVar), cnt.copy(), UAdd.mk(cnt.copy(), UConst.mk(-1)));
            UTerm leftSecondTerm = UMul.mk(sum2.copy(), sum2.copy());
            UTerm equalPred = UPred.mk(EQ, UName.mk("="), List.of(UAdd.mk(leftFirstTerm, leftSecondTerm), rightTerm));
            UTerm cntGreatPred = UPred.mk(GT, UName.mk(">"), List.of(cnt.copy(), UConst.one()));
            UTerm cntEqualPred = UPred.mk(EQ, UName.mk("="), List.of(cnt.copy(), UConst.one()));
            UTerm isNullPred = mkIsNullPred(outProjVar);
            aggTerm = UAdd.mk(UMul.mk(cntGreatPred, equalPred), UMul.mk(cntEqualPred, isNullPred));
          }
          default -> {
            return null;
          }
        }
        aggTerm = replaceAllBoundedVars(aggTerm);
        subTerms.add(aggTerm);
      }
      return UMul.mk(subTerms);
    }

    private static boolean isAggregateExpression(Expression expr) {
      if (ExprKind.Aggregate.isInstance(expr.template())) return true;
      if (ExprKind.FuncCall.isInstance(expr.template())) {
        // MySQL ast parser cannot recognize `AVG(*)` as an aggregate function
        final String name = expr.template().$(ExprFields.FuncCall_Name).$(Name2_1);
        if ("avg".equalsIgnoreCase(name) || "average".equalsIgnoreCase(name)) return true;
      }
      return false;
    }

    private static String getAggregateFunction(Expression expr) {
      assert isAggregateExpression(expr);
      if (ExprKind.Aggregate.isInstance(expr.template())) {
        return expr.template().$(ExprFields.Aggregate_Name);
      } else if (ExprKind.FuncCall.isInstance(expr.template())) {
        return expr.template().$(ExprFields.FuncCall_Name).$(Name2_1);
      }
      return null;
    }

    /**
     * U-expr Normalization and rewriting functions
     */
    private UTerm normalize(UTerm expr) {
      return new QueryUExprNormalizer(expr, schema, this).normalizeTerm();
    }

    private UTerm commonNormalize(UTerm expr) {
      return new QueryUExprNormalizer(expr, schema, this, icFreshVars).commonNormalizeTerm();
    }

    private UTerm normalizeRegroup(UTerm expr, Set<UVar> boundVarSet) {
      return new QueryUExprNormalizer(expr, schema, this).normalizeTermRegroup(boundVarSet);
    }

    private UTerm  normalizeWithIntegrityConstraints(UTerm expr) {
      QueryUExprICRewriter icRewriter = new QueryUExprICRewriter(expr, schema, this);
      expr = icRewriter.normalizeTerm();
      icFreshVars.addAll(icRewriter.getIcFreshVars());
      return expr;
    }

    /**
     * Inner-classes for normalization and rewritings
     */


  }

  /**
   * Inner-classes data structures used for U-expr translation
   */
  static class ComposedUTerm {
    // (p1 /\ v1) \/ (p2 /\ v2) \/ ...
    private final List<Pair<UTerm, UTerm>> preCondAndValues;

    private boolean subQuery = false;

    private UVar subQueryOutVar = null;

    ComposedUTerm(List<Pair<UTerm, UTerm>> preCondAndValues) {
      this.preCondAndValues = preCondAndValues;
    }

    ComposedUTerm(UTerm preCond, UTerm value) {
      this.preCondAndValues = new ArrayList<>();
      preCondAndValues.add(Pair.of(preCond, value));
    }

    ComposedUTerm(UTerm value) {
      this.preCondAndValues = new ArrayList<>();
      preCondAndValues.add(Pair.of(UConst.one(), value));
    }

    ComposedUTerm(UTerm value, UVar subQueryOutVar) {
      this.preCondAndValues = new ArrayList<>();
      preCondAndValues.add(Pair.of(UConst.one(), value));
      this.subQuery = true;
      this.subQueryOutVar = subQueryOutVar;
    }

    ComposedUTerm() {
      this.preCondAndValues = new ArrayList<>();
    }

    void appendTermPair(UTerm preCond, UTerm value) {
      this.preCondAndValues.add(Pair.of(preCond, value));
    }

    UTerm toPredUTerm() {
      // return [p1] * v1 + [p2] * v2 + ...
      final List<UTerm> subTerms = new ArrayList<>();
      for (var pair : preCondAndValues) {
        subTerms.add(UMul.mk(pair.getLeft(), pair.getRight()).copy());
      }

      return UExprSupport.normalizeExpr(UAdd.mk(subTerms));
    }

    static ComposedUTerm doUnaryOp(ComposedUTerm pred0, UnaryOpKind opKind) {
      final List<Pair<UTerm, UTerm>> pair = new ArrayList<>();
      for (var pair0 : pred0.preCondAndValues) {
        final UTerm preCond = pair0.getLeft();
        final UTerm value = pair0.getRight();
        final UTerm finalValue;
        switch (opKind) {
          case UNARY_MINUS -> {
            if (value.kind() == CONST) {
              final Integer V = ((UConst) value).value();
              finalValue = UConst.mk(-V);
            } else throw new IllegalArgumentException("Unsupported unary operator: " + opKind);
          }
          case NOT -> {
            if(value.kind() == CONST) {
              if(value.equals(UConst.nullVal()))
                finalValue = value.copy();
              // TODO: handler other cases for finalValue
              else throw new IllegalArgumentException("Unsupported unary operator: " + opKind);
            } else {
              finalValue = UNeg.mk(value.copy());
            }
          }
          default -> throw new IllegalArgumentException("Unsupported unary operator: " + opKind);
        }
        pair.add(Pair.of(preCond, finalValue));
      }
      return ComposedUTerm.mk(pair);
    }

    static ComposedUTerm doArithmeticOp(ComposedUTerm pred0, ComposedUTerm pred1, BinaryOpKind opKind) {
      assert opKind.isArithmetic();
      final List<Pair<UTerm, UTerm>> pair = new ArrayList<>();
      for (var pair0 : pred0.preCondAndValues) {
        for (var pair1 : pred1.preCondAndValues) {
          final UTerm preCond0 = pair0.getLeft(), preCond1 = pair1.getLeft();
          final UTerm value0 = pair0.getRight(), value1 = pair1.getRight();
          final UTerm combinedPreCond;
          if (preCond0.equals(UConst.ONE)) combinedPreCond = preCond1.copy();
          else if (preCond1.equals(UConst.ONE)) combinedPreCond = preCond0.copy();
          else combinedPreCond = UMul.mk(preCond0.copy(), preCond1.copy());
          final UTerm combinedValue;
          switch (opKind) {
            case PLUS -> combinedValue = UAdd.mk(value0.copy(), value1.copy());
            case MULT -> combinedValue = UMul.mk(value0.copy(), value1.copy());
            case MINUS -> {
              if (value0.kind() == CONST && value1.kind() == CONST) {
                final Integer lhsV = ((UConst) value0).value(), rhsV = ((UConst) value1).value();
                if (lhsV - rhsV >= 0)
                  combinedValue = UConst.mk(lhsV - rhsV);
                else throw new IllegalArgumentException("Unsupported binary operator: " + opKind);
              } else {
                UName funcName = UName.mk("minus");
                combinedValue = UFunc.mk(UFunc.FuncKind.INTEGER, funcName, List.of(value0, value1));
              }
            }
            case DIV -> {
              if (value0.kind() == CONST && value1.kind() == CONST) {
                final Integer lhsV = ((UConst) value0).value(), rhsV = ((UConst) value1).value();
                if (rhsV * (lhsV / rhsV) == lhsV)
                  combinedValue = UConst.mk(lhsV / rhsV);
                else throw new IllegalArgumentException("Unsupported binary operator: " + opKind);
              } else {
                UName funcName = UName.mk("divide");
                combinedValue = UFunc.mk(UFunc.FuncKind.INTEGER, funcName, List.of(value0, value1));
              }
            }
            default -> throw new IllegalArgumentException("Unsupported binary operator: " + opKind);
          }
          pair.add(Pair.of(combinedPreCond, combinedValue));
        }
      }

      return ComposedUTerm.mk(pair);
    }

    static UTerm doComparatorOp(ComposedUTerm pred0, ComposedUTerm pred1, BinaryOpKind opKind) {
      assert opKind.isComparison();
      final List<UTerm> subTerms = new ArrayList<>();
      for (var pair0 : pred0.preCondAndValues) {
        for (var pair1 : pred1.preCondAndValues) {
          final UTerm preCond0 = pair0.getLeft(), preCond1 = pair1.getLeft();
          final UTerm value0 = pair0.getRight(), value1 = pair1.getRight();
          final UTerm combinedPreCond;
          if (preCond0.equals(UConst.ONE)) combinedPreCond = preCond1.copy();
          else if (preCond1.equals(UConst.ONE)) combinedPreCond = preCond0.copy();
          else combinedPreCond = UMul.mk(preCond0.copy(), preCond1.copy());
          final UTerm compareTerm;
          if (opKind == BinaryOpKind.IS) {
            // Also used in `mkProjEqCond` for tuple's attribute mapping
            if (value0.equals(UConst.NULL)) compareTerm = mkIsNullPred(value1.copy());
            else if (value1.equals(UConst.NULL)) compareTerm = mkIsNullPred(value0.copy());
            else compareTerm = UPred.mkBinary(EQ, value0.copy(), value1.copy());
          } else if (opKind == BinaryOpKind.NULL_SAFE_EQUAL) {
            // Also used in `mkProjEqCond` for tuple's attribute mapping
            if (value0.equals(UConst.NULL)) compareTerm = mkIsNullPred(value1.copy());
            else if (value1.equals(UConst.NULL)) compareTerm = mkIsNullPred(value0.copy());
            else compareTerm = UPred.mkBinary(EQ, value0.copy(), value1.copy());
          }
          else {
            // But `mkInSubEqCond` uses code here, since attrs of In sub-query should be not NULL
            if (value0.equals(UConst.NULL) || value1.equals(UConst.NULL))
              compareTerm = UConst.zero();
            else {
              final UPred.PredKind uPredOp = QueryTranslator.castBinaryOp2UPredOp(opKind);
              final UTerm comp = UPred.mkBinary(uPredOp, value0.copy(), value1.copy());
              if (uPredOp == EQ && value0.kind() == VAR && value1.kind() == VAR)
                compareTerm = UMul.mk(comp, mkNotNullPred(value0.copy()));
              else compareTerm = comp;
            }
          }
          subTerms.add(combinedPreCond.equals(UConst.ONE) ? compareTerm : UMul.mk(combinedPreCond, compareTerm));
        }
      }
      return UAdd.mk(subTerms);
    }

    static ComposedUTerm doLogicOp(ComposedUTerm pred0, ComposedUTerm pred1, BinaryOpKind opKind) {
      assert opKind.isLogic();
      final List<Pair<UTerm, UTerm>> pair = new ArrayList<>();
      for (var pair0 : pred0.preCondAndValues) {
        for (var pair1 : pred1.preCondAndValues) {
          final UTerm preCond0 = pair0.getLeft(), preCond1 = pair1.getLeft();
          final UTerm value0 = pair0.getRight(), value1 = pair1.getRight();
          final UTerm combinedPreCond;
          if (preCond0.equals(UConst.ONE)) combinedPreCond = preCond1.copy();
          else if (preCond1.equals(UConst.ONE)) combinedPreCond = preCond0.copy();
          else combinedPreCond = UMul.mk(preCond0.copy(), preCond1.copy());
          final UTerm combinedValue;
          switch (opKind) {
            case OR -> combinedValue = UAdd.mk(value0.copy(), value1.copy());
            case AND -> combinedValue = UMul.mk(value0.copy(), value1.copy());
            default -> throw new IllegalArgumentException("Unsupported binary operator: " + opKind);
          }
          pair.add(Pair.of(combinedPreCond, combinedValue));
        }
      }

      return ComposedUTerm.mk(pair);
    }

    static UTerm mkFuncCall(UFunc.FuncKind funcKind, UName funcName, List<ComposedUTerm> arguments) {
      List<UTerm> funcArguments = new ArrayList<>();
      for(ComposedUTerm composedArg : arguments) {
//        assert composedArg.preCondAndValues.size() == 1;
//        final UTerm left = composedArg.preCondAndValues.get(0).getLeft();
//        assert left.equals(UConst.ONE);
        funcArguments.add(composedArg.toPredUTerm());
      }
      return UFunc.mk(funcKind, funcName, funcArguments);
    }

    UVar getSubQueryOutVar() {
      if(this.subQuery) return subQueryOutVar;
      return null;
    }

    void replaceVar(UVar baseVar, UVar repVar) {
      for(Pair<UTerm, UTerm> pair : this.preCondAndValues) {
        pair.getRight().replaceVarInplace(baseVar, repVar, false);
      }
    }

    static ComposedUTerm mk(List<Pair<UTerm, UTerm>> preCondAndValues) {
      return new ComposedUTerm(preCondAndValues);
    }

    static ComposedUTerm mk(UTerm preCond, UTerm value) {
      return new ComposedUTerm(preCond, value);
    }

    static ComposedUTerm mk(UTerm value) {
      return new ComposedUTerm(value);
    }

    static ComposedUTerm mk(UTerm value, UVar subQueryOutVar) { return new ComposedUTerm(value, subQueryOutVar); }

    static ComposedUTerm mk() {
      return new ComposedUTerm();
    }
  }

  static class VALUESTable {
    final Map<TupleInstance, Integer> tupleMultiSet;
    final List<String> schema;

    VALUESTable(List<TupleInstance> tuples, List<String> schema) {
      this.tupleMultiSet = new HashMap<>();
      this.schema = schema;
      for (TupleInstance tuple : tuples)
        tupleMultiSet.put(tuple, tupleMultiSet.getOrDefault(tuple, 0) + 1);
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (o == null || getClass() != o.getClass()) return false;
      VALUESTable valuesTable = (VALUESTable) o;
      return Objects.equals(tupleMultiSet, valuesTable.tupleMultiSet) && Objects.equals(schema, valuesTable.schema);
    }

    @Override
    public int hashCode() {
      return Objects.hash(tupleMultiSet, schema);
    }

    static VALUESTable parse(String str, List<String> defaultSchema) {
      final List<TupleInstance> tuples = new ArrayList<>();
      final List<String> schema = new ArrayList<>();
      // `str` = (VALUES (1, 2), (3, 4)) or (VALUES)
      String data = str.substring(7, str.length() - 1); // (1, 2), (3, 4)
      data = data.replaceAll(" ", ""); // (1,2),(3,4)
      if (data.isEmpty()) // (VALUES) is an empty table
        return new VALUESTable(tuples, coalesce(defaultSchema, schema));

      final String[] tupleList = data.substring(1, data.length() - 1).split("\\),\\(");
      for (String tuple : tupleList) {
        // tuple = 1,2
        final List<String> valueStrs = Arrays.stream(tuple.split(",")).toList();
        final List<Integer> values = new ArrayList<>(valueStrs.size());
        for (String vs : valueStrs) {
          // If vs is a string, wrapped by '', or NULL value
          if (!Character.isDigit(vs.charAt(0))) {
            if ("NULL".equals(vs)) values.add(null);
            else if("TRUE".equals(vs)) values.add(1);
            else if("FALSE".equals(vs)) values.add(0);
            else values.add(vs.substring(1, vs.length() - 1).hashCode());
          } else values.add(Integer.parseInt(vs));
        }
        tuples.add(new TupleInstance(values));
      }
      if (tuples.size() > 0) {
        final int schemaLength = tuples.get(0).size();
        for (int i = 0; i < schemaLength; ++i)
          schema.add("expr$" + i);
      }
      return new VALUESTable(tuples, coalesce(defaultSchema, schema));
    }
  }

  class VALUESTableParser {
    private final NameSequence tableSeq;
    private final String sql0, sql1;
    private final Schema baseSchema;

    VALUESTableParser(String sql0, String sql1, Schema baseSchema) {
      this.sql0 = sql0;
      this.sql1 = sql1;
      this.tableSeq = NameSequence.mkIndexed("r", 0);
      this.baseSchema = baseSchema;
    }

    void parse() {
      final String modifiedSql0 = registerVALUESTable(sql0);
      final String modifiedSql1 = registerVALUESTable(sql1);
      schema = initSchema(baseSchema);
      p0 = parsePlan(modifiedSql0, schema);
      p1 = parsePlan(modifiedSql1, schema);
    }

    private String registerVALUESTable(String sql) {
      // `SELECT * FROM VALUES()` -> `SELECT * FROM R`, R: [expr$0, expr$1, ...]
      // find patterns of `(VALUES  (30, 3))`
      sql = sql.replaceAll("ROW", "");
      while (sql.contains("(VALUES")) {
        final int start = sql.indexOf("(VALUES");
        int count = 0, idx0 = start;
        for (int bound = sql.length(); idx0 < bound; ++idx0) {
          if (sql.charAt(idx0) == '(') ++count;
          if (sql.charAt(idx0) == ')') {
            --count;
            if (count == 0) break;
          }
        }
        if (idx0 == sql.length()) {
          assert false : "wrong pattern of VALUES()";
          return null;
        }
        final String VALUESInfo = sql.substring(start, idx0 + 1); // `(VALUES  (30, 3))`
        // For case of `(VALUES) as t(col, ..)` -> r0 as t, and pick schema info in t(col, ..)
        idx0++;
        List<String> schema = null;
        if (idx0 < sql.length() && sql.substring(idx0).trim().toUpperCase().startsWith("AS")) {
          final int aliasStart = sql.toUpperCase().indexOf("AS", idx0) + 3;
          final int aliasEnd;
          int idx1 = aliasStart;
          while (idx1 < sql.length() && (sql.charAt(idx1) != ' ' && sql.charAt(idx1) != '('))
            idx1++;
          final String aliasName = sql.substring(aliasStart, idx1);

          while (idx1 < sql.length() && sql.charAt(idx1) == ' ')
            idx1++;
          if (idx1 < sql.length() && sql.charAt(idx1) == '(') {
            while (idx1 < sql.length() && sql.charAt(idx1) != '(')
              idx1++;
            aliasEnd = sql.indexOf(")", idx1) + 1;
            final String schemaStr = sql.substring(idx1, aliasEnd);
            schema = Arrays.stream(schemaStr.substring(1, schemaStr.length() - 1).split(", ")).toList();
            final String aliasAll = sql.substring(aliasStart, aliasEnd);
            sql = sql.replace(aliasAll, aliasName);
          }
        }
        final VALUESTable valuesTable = VALUESTable.parse(VALUESInfo, schema);
        if (VALUESTablesReg.get(valuesTable) == null)
          VALUESTablesReg.put(valuesTable, tableSeq.next());
        sql = sql.replace(VALUESInfo, VALUESTablesReg.get(valuesTable));
      }
      return sql;
    }

    private Schema initSchema(Schema baseSchema) {
      StringBuilder builder = new StringBuilder();
      for (String table : VALUESTablesReg.values()) {
        builder.append("CREATE TABLE `").append(table).append("`(\n");
        final List<String> columns = VALUESTablesReg.inverse().get(table).schema;
        for (String col : columns) {
          builder.append("`").append(col).append("` int");
          if (columns.indexOf(col) == columns.size() - 1) builder.append("\n");
          else builder.append(",\n");
        }
        if (columns.isEmpty()) {
          builder.append("`expr$0` int").append("\n");
        }
        builder.append(");\n");
      }
      // Combine with baseSchema
      if (baseSchema != null)
        builder.append(baseSchema.toDdl(baseSchema.dbType(), builder));

      return Schema.parse(MySQL, builder.toString());
    }

    private PlanContext parsePlan(String sql, Schema schema) {
      final SqlNode sqlNode = parseSql(MySQL, sql);
      if (sqlNode == null) return null;

      sqlNode.context().setSchema(schema);
      // NormalizationSupport.normalizeAst(sqlNode);

      return assemblePlan(sqlNode, schema);
    }
  }

  record TupleInstance(List<Integer> values) {
    Integer getValue(int index) {
      if (values == null || index >= values.size()) return null;
      return values.get(index);
    }

    int size() {
      if (values == null) return 0;
      return values.size();
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (o == null || getClass() != o.getClass()) return false;
      TupleInstance that = (TupleInstance) o;
      return Objects.equals(values, that.values);
    }

    @Override
    public int hashCode() {
      return Objects.hash(values);
    }

    static TupleInstance mk(List<Integer> values) {
      return new TupleInstance(values);
    }
  }

  record TupleInstanceStr(List<String> values) {
    String getValue(int index) {
      if (values == null || index >= values.size()) return null;
      return values.get(index);
    }

    int size() {
      if (values == null) return 0;
      return values.size();
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (o == null || getClass() != o.getClass()) return false;
      TupleInstanceStr that = (TupleInstanceStr) o;
      return Objects.equals(values, that.values);
    }

    @Override
    public int hashCode() {
      return Objects.hash(values);
    }

    static TupleInstanceStr mk(List<String> values) {
      return new TupleInstanceStr(values);
    }
  }
}

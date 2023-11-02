package wtune.superopt.uexpr.normalizer;

import wtune.common.utils.NameSequence;
import wtune.common.utils.NaturalCongruence;
import wtune.sql.ast.constants.ConstraintKind;
import wtune.sql.plan.Value;
import wtune.sql.schema.Column;
import wtune.sql.schema.Constraint;
import wtune.sql.schema.Schema;
import wtune.sql.schema.Table;
import wtune.superopt.uexpr.*;

import java.util.*;
import java.util.function.Function;

import static wtune.common.utils.IterableSupport.*;
import static wtune.common.utils.ListSupport.filter;
import static wtune.common.utils.ListSupport.map;
import static wtune.superopt.uexpr.UExprConcreteTranslator.QueryTranslator.globalExpr;
import static wtune.superopt.uexpr.normalizer.QueryUExprNormalizer.buildNaturalCongruence;
import static wtune.superopt.uexpr.UExprSupport.*;
import static wtune.superopt.uexpr.UKind.*;
import static wtune.superopt.uexpr.UKind.NEGATION;
import static wtune.superopt.uexpr.UPred.PredKind.EQ;

public class QueryUExprICRewriter extends UNormalization {
  private Schema schema;

  private static final String VAR_NAME_PREFIX = "y";
  private final List<UVar> icFreshVars;

  private final List<UVar> boundedStackVars;

  private final UExprConcreteTranslator.QueryTranslator translator;

  private UVar replaceVarOneRecord;

  private final NameSequence tupleVarSeq;

  private static int selectedIC = -1;
  private static boolean hasIC = true;

  public static void selectIC(int index) {
    selectedIC = index;
  }

  public static int selectedIC() {
    return selectedIC;
  }

  public static void setHasIC(boolean val) {
    hasIC = val;
  }

  public static boolean hasIC() {
    return hasIC;
  }

  public UVar mkFreshICRewriterBaseVar() {
    UVar newVar = UVar.mkBase(UName.mk(tupleVarSeq.next()));
    return newVar;
  }

  public List<UVar> getIcFreshVars() {
    return this.icFreshVars;
  }

  public QueryUExprICRewriter(UTerm expr, Schema schema, UExprConcreteTranslator.QueryTranslator translator) {
    super(expr);
    this.schema = schema;
    this.icFreshVars = new ArrayList<>();
    this.boundedStackVars = new ArrayList<>();
    this.replaceVarOneRecord = null;
    this.translator = translator;
    this.tupleVarSeq = NameSequence.mkIndexed(VAR_NAME_PREFIX, 0);
  }

  @Override
  public UTerm normalizeTerm() {
    do {
      expr = new QueryUExprNormalizer(expr, schema, translator).normalizeTerm();
      globalExpr = expr;
      isModified = false;
      expr = performNormalizeRule(this::applyReference);
      expr = performNormalizeRule(this::applyPrimary);
      expr = performNormalizeRule(this::applyForeign);
      expr = performNormalizeRule(this::rewritePrimary);
      expr = performNormalizeRule(this::removeNotNull);
      expr = performNormalizeRule(this::applyPrimary1);
    } while (isModified);
    return expr;
  }

  @Override
  protected UTerm performNormalizeRule(Function<UTerm, UTerm> transformation) {
    expr = transformation.apply(expr);
    expr = new QueryUExprNormalizer(expr, schema, translator).normalizeTerm();
    return expr;
  }

  /**
   * Reference(R0, a0, R1, a1):
   * \sum_{t1}(R0(t0) * R1(t1) * [a0(t0) = a1(t1)] * not([IsNull(a0(t0))])) -> R0(t0) * not([IsNull(a0(t0))]))
   */
  private UTerm applyReference(UTerm expr) {
    return expr;
  }

  /**
   * Unique(R, a) eliminate self-join
   * R(t1) * R(t2) * [a(t1) = a(t2)] -> R(t1) * [t1 = t2]
   * Unique(R, a) add squash
   * \sum_{t}([a(t) = e] * R(t) * f(t)) -> || \sum_{t}([a(t) = e] * R(t) * f(t)) ||
   *
   * \sum_{t}(R(t) * g(t)) -> \sum_{t}||R(t) * g(t)||, g(t) does not contain [a(t) = e]
   */
  private UTerm applyPrimary(UTerm expr) {
    final List<Constraint> uniques = new ArrayList<>();
    if (selectedIC < 0) {
      for (Table table : schema.tables()) {
        table.constraints(ConstraintKind.PRIMARY).forEach(uniques::add);
      }
    } else {
      // select the selectedIC-th nonempty IC
      int nonemptyICIndex = 0;
      for (Table table : schema.tables()) {
        table.constraints(ConstraintKind.PRIMARY).forEach(uniques::add);
        if (!uniques.isEmpty() && nonemptyICIndex < selectedIC) {
          uniques.clear();
          nonemptyICIndex = nonemptyICIndex + 1;
        } else if (!uniques.isEmpty()) {
          break;
        }
      }
      hasIC = !uniques.isEmpty();
    }
    Collections.reverse(uniques);
    // TODO: multiple columns on Unique constraint?
    expr = applyUniqueOnSelfJoin(expr, uniques);
    expr = removeUnusedSummationBoundedVar(expr);
    expr = applyUniqueAddSquash(expr, uniques);
    expr = applyUniqueRemoveNull(expr, uniques);
    expr = applyUniqueRemoveNullCongruence(expr, uniques);
    expr = applyUniqueSplitSquashAdd(expr, uniques);
    return expr;
  }

  // apply foreign key constraint to normalize
  private UTerm applyForeign(UTerm expr) {
    final List<Constraint> primarys = new ArrayList<>();
    final List<Constraint> foreigns = new ArrayList<>();
    for (Table table : schema.tables()) {
      table.constraints(ConstraintKind.PRIMARY).forEach(primarys::add);
      table.constraints(ConstraintKind.FOREIGN).forEach(foreigns::add);
    }
//    expr = applyForeignRemoveNullUnique(expr, primarys, foreigns);
    expr = applyForeignRemoveRedundantBoundVar(expr, primarys, foreigns);
    return expr;
  }

  // place the rule here since it needs to be applied based on previous results
  private UTerm applyPrimary1(UTerm expr) {
    final List<Constraint> uniques = new ArrayList<>();
    if(selectedIC < 0) {
      for (Table table : schema.tables()) {
        table.constraints(ConstraintKind.PRIMARY).forEach(uniques::add);
      }
    } else {
      // select the selectedIC-th nonempty IC
      int nonemptyICIndex = 0;
      for (Table table : schema.tables()) {
        table.constraints(ConstraintKind.PRIMARY).forEach(uniques::add);
        if (!uniques.isEmpty() && nonemptyICIndex < selectedIC) {
          uniques.clear();
          nonemptyICIndex = nonemptyICIndex + 1;
        } else if (!uniques.isEmpty()) {
          break;
        }
      }
      hasIC = !uniques.isEmpty();
    }
    Collections.reverse(uniques);
    expr = applyUniqueRemoveOneRecordSum(expr, uniques);
    expr = applyUniqueMergeSumSquashAdd(expr, uniques);
    return expr;
  }

  // R(t1) * R(t2) * [a(t1) = a(t2)] -> R(t1) * [t1 = t2]
  private UTerm applyUniqueOnSelfJoin(UTerm expr, List<Constraint> uniques) {
    expr = transformSubTerms(expr, t -> applyUniqueOnSelfJoin(t, uniques));
    if (expr.kind() != MULTIPLY) return expr;

    final NaturalCongruence<UVar> varEqClass = UExprSupport.getEqVarCongruenceInTermsOfMul(expr);
    final UMul mul = (UMul) expr;
    final List<UTerm> subTerms = mul.subTerms();
    for (Constraint unique : uniques) {
      if(unique.columns().size() != 1) continue;
      final Column column = unique.columns().get(0);
      final UName colName = UName.mk(column.toString()), tableName = UName.mk(column.tableName());
      final List<UTerm> tables = filter(subTerms, t -> t.kind() == TABLE && ((UTable) t).tableName().equals(tableName));

      final List<UVar> eqVars = varEqClass.keys().stream().toList();
      for (int i = 0, bound = eqVars.size(); i < bound; ++i) {
        final UVar var0 = eqVars.get(i);
        for (int j = i + 1, bound0 = eqVars.size(); j < bound0; ++j) {
          final UVar var1 = eqVars.get(j);
          if (var0.equals(var1) || !varEqClass.isCongruent(var0, var1)) continue;
          if (!var0.name().equals(colName) || !var1.name().equals(colName)) continue;
          final UVar baseVar0 = var0.args()[0], baseVar1 = var1.args()[0];
          assert baseVar0.is(UVar.VarKind.BASE) && baseVar1.is(UVar.VarKind.BASE);
          final UTerm table0 = linearFind(tables, t -> ((UTable) t).var().equals(baseVar0));
          final UTerm table1 = linearFind(tables, t -> ((UTable) t).var().equals(baseVar1));
          if (table0 == null || table1 == null) continue;
          // Do rewrite here
          mul.subTerms().remove(table1);
          mul.replaceVarInplace(baseVar1, baseVar0, false);
          isModified = true;
        }
      }
    }
    return expr;
  }

  // naive
  private UTerm removeUnusedSummationBoundedVar(UTerm expr) {
    expr = transformSubTerms(expr, this::removeUnusedSummationBoundedVar);
    if (expr.kind() != SUMMATION) return expr;

    ((USum) expr).removeUnusedBoundedVar();
    return expr;
  }

  /** \sum_{t}(R(t) * g(t)) -> \sum_{t}||R(t) * g(t)||, g(t) does not contain [a(t) = e]
   * */
  public UTerm applyUniqueAddSquashInner(UTerm expr, List<Constraint> uniques, boolean consider) {
    boolean thisConsider = (expr.kind() == MULTIPLY
                            || expr.kind() == ADD) ? consider : !expr.kind().isUnary();
    expr = transformSubTerms(expr, t -> applyUniqueAddSquashInner(t, uniques, thisConsider));
    if (expr.kind() != SUMMATION || !consider) return expr;

    final USum summation = (USum) expr;
    final List<UTerm> subTerms = summation.body().subTerms();
    final Set<UTerm> squashedTerms = new HashSet<>(summation.body().subTerms().size());

    for (Constraint unique : uniques) {
      if (unique.columns().size() > 1){
        continue;
      }
      final Column column = unique.columns().get(0);
      final UName colName = UName.mk(column.toString()), tableName = UName.mk(column.tableName());
      for (UVar boundedVar : summation.boundedVars()) {
        final UTerm tableTerm =
                linearFind(subTerms, t -> !squashedTerms.contains(t) && t.equals(UTable.mk(tableName, boundedVar)));
        final UVarTerm projVarTerm = UVarTerm.mk(UVar.mkProj(colName, boundedVar));
        final UTerm predTerm =
                linearFind(subTerms, t -> !squashedTerms.contains(t) && isEqVarFreeTerm(t, projVarTerm));
        if (tableTerm == null) continue;

        if (predTerm != null) continue;
        squashedTerms.addAll(filter(subTerms, t -> t.isUsing(boundedVar) && !(t.kind() == VAR)));
      }
    }


    if (!squashedTerms.isEmpty()) {
      isModified = true;
      summation.body().subTerms().removeAll(squashedTerms);
      final UTerm newSquashBody = UMul.mk(new ArrayList<>(squashedTerms));
      final USquash newSquash = USquash.mk(newSquashBody);
      summation.body().subTerms().add(newSquash);
    }
    return summation;
  }

  /** \sum_{t}([a(t) = e] * R(t) * f(t)) -> || \sum_{t}([a(t) = e] * R(t) * f(t)) ||
   * */
  public UTerm applyUniqueAddSquashOuter(UTerm expr, List<Constraint> uniques) {
    if (expr.kind().isUnary()) return expr;
    expr = transformSubTerms(expr, t -> applyUniqueAddSquashOuter(t, uniques));
    if (expr.kind() != SUMMATION) return expr;

    final USum summation = (USum) expr;
    final List<UTerm> subTerms = summation.body().subTerms();
    final Set<UTerm> squashedTerms = new HashSet<>(summation.body().subTerms().size());
    final Set<UVar> squashedVars = new HashSet<>(summation.boundedVars().size());

    for (Constraint unique : uniques) {
      if (unique.columns().size() > 1){
        continue;
      }
      final Column column = unique.columns().get(0);
      final UName colName = UName.mk(column.toString()), tableName = UName.mk(column.tableName());
      for (UVar boundedVar : filter(summation.boundedVars(), v -> !squashedVars.contains(v))) {
        final UTerm tableTerm =
                linearFind(subTerms, t -> !squashedTerms.contains(t) && t.equals(UTable.mk(tableName, boundedVar)));
        final UVarTerm projVarTerm = UVarTerm.mk(UVar.mkProj(colName, boundedVar));
        final UTerm predTerm =
                linearFind(subTerms, t -> !squashedTerms.contains(t) && isEqVarFreeTerm(t, projVarTerm));
        if (tableTerm == null) continue;

        squashedTerms.addAll(filter(subTerms, t -> t.isUsing(boundedVar) && !(t.kind() == VAR)));
        if ((predTerm != null) && !any(subTerms, t -> t.isUsing(boundedVar) && (t.kind() == VAR)))
          squashedVars.add(boundedVar);
      }
    }


    if (!squashedTerms.isEmpty() && !squashedVars.isEmpty()) {
      isModified = true;
      summation.body().subTerms().removeAll(squashedTerms);
      for (UVar removedVar : squashedVars) {
        summation.removeBoundedVar(removedVar);
      }
      final UTerm newSquashBody = USum.mk(squashedVars, UMul.mk(new ArrayList<>(squashedTerms)));
      final USquash newSquash = USquash.mk(newSquashBody);
      summation.body().subTerms().add(newSquash);
    }
    if (summation.boundedVars().isEmpty()) return summation.body();
    return summation;
  }

  public UTerm applyUniqueAddSquash(UTerm expr, List<Constraint> uniques) {
    expr = applyUniqueAddSquashInner(expr, uniques, true);
    expr = applyUniqueAddSquashOuter(expr, uniques);
    return expr;
  }

  // [IsNull(a)] && a is PRIMARY -> [IsNull(a)] = 0
  public UTerm applyUniqueRemoveNull(UTerm expr, List<Constraint> uniques) {
    expr = transformSubTerms(expr, t -> applyUniqueRemoveNull(t, uniques));
    if (!isNullPred(expr)) return expr;
    UPred pred = (UPred) expr;
    assert pred.args().size() == 1;

    if(pred.args().get(0).kind() != VAR) return expr;
    UVar targetVar = ((UVarTerm) pred.args().get(0)).var();

    if(!targetVar.is(UVar.VarKind.PROJ)) return expr;
    UName targetColName = targetVar.name();

    for(Constraint unique : uniques) {
      // check unique column whether exist
      for(Column uniqueColumn : unique.columns()) {
        if(Objects.equals(uniqueColumn.toString(), targetColName.toString())) { // it is unique!
          return UConst.zero();
        }
      }
    }

    return expr;
  }

  // [a = b] && a is PRIMARY -> [IsNull(b)] = 0
  public UTerm applyUniqueRemoveNullCongruence(UTerm expr, List<Constraint> uniques) {
    expr = transformSubTerms(expr, t -> applyUniqueRemoveNullCongruence(t, uniques));
    if (expr.kind() != MULTIPLY) return expr;
    final List<UTerm> subTerms = expr.subTerms();
    // newSubTerms, should change isNull(b) -> 0 or notNull(b) -> 1
    final NaturalCongruence<UVar> varEqClass = UExprSupport.getEqVarCongruenceInTermsOfMul(expr);
    final List<UVar> eqVars = varEqClass.keys().stream().toList();

    // check whether primary key exist in congruence
    for (final Constraint unique : uniques) {
      for (final Column uniqueColumn : unique.columns()) {
        for (final UVar eqVar : eqVars) {
          boolean apply = false;
          Set<UVar> congruence = varEqClass.eqClassAt(eqVar);
          for(UVar tgtVar : congruence) {
            if (tgtVar.kind() == UVar.VarKind.PROJ
                    && Objects.equals(tgtVar.name().toString(), uniqueColumn.toString())) {
              apply = true;
              break;
            }
          }
          if(apply) {
            // newSubTerms, should change isNull(b) -> 0 or notNull(b) -> 1
            boolean applied = false;
            List<UTerm> newSubTerms = new ArrayList<>();
            for(final UTerm subTerm : subTerms) {
              boolean isNeg = false;
              UTerm targetTerm = subTerm;
              if(targetTerm.kind() == NEGATION) {
                targetTerm = targetTerm.subTerms().get(0);
                isNeg = true;
              }
              if(isNullPred(targetTerm)) {
                UPred isNullPred = (UPred) targetTerm;
                UTerm arg = isNullPred.args().get(0);
                if(arg.kind() == VAR) {
                  UVar tgtVar = ((UVarTerm) arg).var();
                  // the case for isNull(b)
                  if(congruence.contains(tgtVar)) {
                    isModified = true;
                    applied = true;
                    targetTerm = UConst.mk(0);
                  }
                }
              }
              newSubTerms.add(isNeg? UNeg.mk(targetTerm) : targetTerm);
            }
            if(applied)
              return UMul.mk(newSubTerms);
          }
        }
      }
    }

    return UMul.mk(subTerms);
  }

  private boolean isColUnique(UName col, List<Constraint> uniques) {
    for(Constraint unique : uniques) {
      if(uniques.size() == 1)
        for(Column column : unique.columns()) {
          if(Objects.equals(column.toString(), col.toString())) return true;
        }
    }
    return false;
  }

  private Set<UTerm> searchProjVarReplaceTerm(UVarTerm tgtTerm, UVar boundedVar, USum sum) {
    Set<UTerm> result = new HashSet<>();
    if(sum.body().kind() != MULTIPLY) return result;
    final List<UTerm> subTerms = sum.body().subTerms();
    for(final UTerm subTerm : subTerms) {
      if(subTerm instanceof UPred pred) {
        if(pred.isPredKind(EQ) && pred.isUsingProjVar(tgtTerm.var())) {
          UTerm toAdd = (pred.args().get(0).isUsingProjVar(tgtTerm.var()))?pred.args().get(1):pred.args().get(0);
          if(!toAdd.isUsing(boundedVar)) result.add(toAdd);
        }
      }
    }

    return result;
  }

  /** ||E * \sum_{t}([a(t) = CONST1]*...*[b(t) = CONST2]) + E * \sum_{t}([a(t) = CONST1]*...*[b(t) = CONST3])||
   && a is unique -> can be split:
   ||E * \sum_{t}([a(t) = CONST1]*...*[b(t) = CONST2])|| + ||E * \sum_{t}([a(t) = CONST1]*...*[b(t) = CONST3])|| * */
  private boolean canSplitSquashAddSum(List<UTerm> tgtTerms, List<Constraint> uniques) {
    List<UTerm> commonTerms = new ArrayList<>(); // commonTerms contain no Sum for every tgtTerm
    List<USum> tgtSums = new ArrayList<>(); // tgtSums contain one sum for every tgtTerm
    for(final UTerm tgtTerm : tgtTerms) {
      // first it must be MULTIPLY or simply SUMMATION
      if(tgtTerm.kind() != MULTIPLY && tgtTerm.kind() != SUMMATION)
        return false;
      if(tgtTerm.kind() == MULTIPLY) { // be MULTIPLY then find its subTerms of SUMMATION
        UMul copyMul = (UMul) tgtTerm.copy();
        List<UTerm> sums = filter(copyMul.subTerms(), t -> t.kind() == SUMMATION);
        if(sums.size() != 1) return false; // MULTIPLY(tgtTerm) should contain only one SUMMATION

        copyMul.subTerms().remove(sums.get(0));
        commonTerms.add(copyMul);
        tgtSums.add((USum) sums.get(0));
      } else if (tgtTerm.kind() == SUMMATION) { // directly add to tgtSums
        tgtSums.add((USum) tgtTerm);
      }
    }

    // only one case should exist, for common case, every commonTerm should equal
    if (commonTerms.size() > 0) {
      if (commonTerms.size() != tgtTerms.size() || tgtSums.size() != tgtTerms.size()) return false;
      for(final UTerm commonTerm : commonTerms) // every commonTerm should equal
        if(!all(commonTerms, t -> t.equals(commonTerm))) return false;
    } else if (tgtSums.size() > 0) {
      if (tgtSums.size() != tgtTerms.size()) return false;
    }

    // only consider one boundedVar situation
    if(!all(tgtSums, s -> s.boundedVars().size() == 1)) return false;

    // now we should examine whether every SUMMATION meet the requirement
    // first add the col and correspoding CONST, such as [a(t) = CONST1] and [b(t) = CONST2]
    // every summation has one Map<UName, UTerm>, which means {a: CONST1, b: CONST2}
    List<Map<UName, UTerm>> valueConstMaps = new ArrayList<>();
    for(final USum tgtSum : tgtSums) {
      final UVar boundedVar = tgtSum.boundedVars().iterator().next();
      List<Value> varSchema = translator.getTupleVarSchema(boundedVar);
      Map<UName, UTerm> valueConstMap = new HashMap<>();
      for(final Value v : varSchema) {
        final UVarTerm targetProjVarTerm = UVarTerm.mk(translator.mkProjVar(v, boundedVar));
        final Set<UTerm> targetProjVarEqTerms = searchProjVarReplaceTerm(targetProjVarTerm, boundedVar, tgtSum);
        if(targetProjVarEqTerms.size() != 1) continue; // only consider one EQ term situation
        valueConstMap.put(targetProjVarTerm.var().name(), targetProjVarEqTerms.iterator().next());
      }
      valueConstMaps.add(valueConstMap);
    }

    // second convert the List into a global map
    Map<UName, List<UTerm>> verifyMaps = new HashMap<>();
    for(final Map<UName, UTerm> valueConstMap : valueConstMaps) {
      for(final UName key : valueConstMap.keySet()) {
        if(!verifyMaps.containsKey(key)) {
          List<UTerm> value = new ArrayList<>();
          value.add(valueConstMap.get(key));
          verifyMaps.put(key, value);
        } else {
          List<UTerm> value = verifyMaps.get(key);
          value.add(valueConstMap.get(key));
          verifyMaps.put(key, value);
        }
      }
    }

    // hasUniquePred -> every summation has same [a(t) = CONST1]
    // hasNoUniquePred -> every summation has not same [b(t) = CONST_NOT_SAME]
    boolean hasUniquePred = false;
    boolean hasNoUniquePred = false;
    for(final UName key : verifyMaps.keySet()) {
      List<UTerm> value = verifyMaps.get(key);
      if(isColUnique(key, uniques)) {
        if(value.size() == tgtTerms.size() && all(value, t -> t.equals(value.get(0)))) {
          hasUniquePred = true;
        }
      } else if(!hasNoUniquePred){
        if(value.size() == tgtTerms.size()) {
          hasNoUniquePred = true;
          for(int i = 0 ; i < value.size(); i++)
            for(int j = 0; j < value.size(); j++)
              if (i != j && value.get(i).equals(value.get(j))) {
                hasNoUniquePred = false;
                break;
              }
        }
      }
      if(hasUniquePred && hasNoUniquePred) break;
    }

    return hasUniquePred && hasNoUniquePred;
  }

  /** ||A + B|| && A and B cannot both > 0 due to constraint -> ||A + B|| = ||A|| + ||B|| * */
  public UTerm applyUniqueSplitSquashAdd(UTerm expr, List<Constraint> uniques) {
    expr = transformSubTerms(expr, t -> applyUniqueSplitSquashAdd(t, uniques));
    if(expr.kind() != SQUASH) return expr;
    if(((USquash) expr).body().kind() != ADD) return expr;

    UAdd body = (UAdd) ((USquash) expr).body();
    if(canSplitSquashAddSum(body.subTerms(), uniques)) {
      List<UTerm> newAddSubTerms = new ArrayList<>();
      all(body.subTerms(), t -> newAddSubTerms.add(USquash.mk(t)));
      return UAdd.mk(newAddSubTerms);
    }

    return expr;
  }

  /** check whether all sums contain same boundedVar (from name to schema) * */
  private boolean checkSumListWithSameBoundedVar(List<USum> targetSums) {
    for(final USum sum : targetSums) {
      for(final UVar boundedVar : sum.boundedVars()) {
        if(!all(targetSums, t -> t.isUsingBoundedVar(boundedVar))) return false;
      }
    }
    return true;
  }

  private boolean checkSumListWithSameEQConst(List<USum> targetSums, List<Constraint> uniques) {
    for(final Constraint unique : uniques) {
      if(unique.columns().size() != 1) continue;
      final Column column = unique.columns().get(0);
      final UName colName = UName.mk(column.toString());
      for(final USum targetSum : targetSums) {
        // here only consider ONE boundedVar case due to checkMergeSumSquashAdd
        final UVarTerm projVarTerm = UVarTerm.mk(UVar.mkProj(colName, targetSum.boundedVars().iterator().next()));
        if(QueryUExprNormalizer.searchEQConstProjVar(projVarTerm.var(),
                                                     targetSum.body().subTerms(),
                                                     targetSum.boundedVars()) != null)
          return true;
      }
    }
    return false;
  }

  /** for ||∑{y}(g(x,y)) * ... + ∑{y}(t(x,y)) * ... +  ... ||
   * check whether g(x,y), t(x,y) all contain  at least a [a(y) = C]
   * and C is a const relative to y, a is unique
   * only consider ONE boundedVar here
   * */
  private UTerm checkMergeSumSquashAdd(USquash squash, List<Constraint> uniques, Set<UVar> newBoundedVars) {
    UTerm body = squash.body();
    UTerm newBody = null;
    List<USum> targetSums = new ArrayList<>();
    // collect all sums
    switch(body.kind()) {
//      case SUMMATION: {
//        if(((USum) body).boundedVars().size() != 1) return squash;
//        targetSums.add((USum) body);
//        break;
//      }
      case ADD: {
        for (UTerm subTerm : body.subTerms()) {
          if(subTerm.kind() == SUMMATION) {
            if(((USum) subTerm).boundedVars().size() != 1) return squash;
            targetSums.add((USum) subTerm);
          }
          else
            return squash;
        }
        break;
      }
      default: return squash;
    }

    if(!checkSumListWithSameBoundedVar(targetSums)) return squash;

    if(!checkSumListWithSameEQConst(targetSums, uniques)) return squash;

    assert targetSums.size() > 0;

    if(targetSums.size() == 1) {
      newBoundedVars.add(targetSums.get(0).boundedVars().iterator().next());
      newBody = targetSums.get(0).body();
    } else {
      newBoundedVars.add(targetSums.get(0).boundedVars().iterator().next());
      List<UTerm> newAddList = new ArrayList<>();
      all(targetSums, t -> newAddList.add(t.body()));
      newBody = UAdd.mk(newAddList);
    }

    isModified = true;

    return USquash.mk(newBody);
  }


  /** ∑{x}(f(x) * ||∑{y}(g(x,y)) * ... + ∑{y}(t(x,y)) * ... +  ... ||)
   * => ∑{x,y}(f(x) * ||(g(x,y)) * ... +(t(x,y)) * ... +  ... ||)
   * and g(x,y), t(x,y) all contain  at least a [a(y) = C], C is a const relative to y, a is unique
   * */
  public UTerm applyUniqueMergeSumSquashAdd(UTerm expr, List<Constraint> uniques) {
    expr = transformSubTerms(expr, t -> applyUniqueMergeSumSquashAdd(t, uniques));
    if(expr.kind() != SUMMATION) return expr;
    if(((USum) expr).body().kind() != MULTIPLY && ((USum) expr).body().kind() != SQUASH) return expr;

    UTerm body = ((USum) expr).body();
    UTerm newBody = null;
    Set<UVar> newBoundedVars = new HashSet<>(((USum) expr).boundedVars());
    switch (body.kind()) {
      case SQUASH: {
        newBody = checkMergeSumSquashAdd((USquash) body, uniques, newBoundedVars);
        break;
      }
      case MULTIPLY: {
        ArrayList<UTerm> newSubTerms = new ArrayList<>();
        for (UTerm subTerm : body.subTerms()) {
          if(subTerm.kind() == SQUASH)
            newSubTerms.add(checkMergeSumSquashAdd((USquash) subTerm, uniques, newBoundedVars));
          else
            newSubTerms.add(subTerm);
        }
        newBody = UMul.mk(newSubTerms);
        break;
      }
      default: newBody = body;
    }

    return USum.mk(newBoundedVars, newBody);
  }

  /** FOREIGN(a -> b) && b is primary then isNull(a) = 0
   * */
  public UTerm applyForeignRemoveNullUnique(UTerm expr, List<Constraint> primarys, List<Constraint> foreigns) {
    expr = transformSubTerms(expr, t -> applyForeignRemoveNullUnique(t, primarys, foreigns));
    if (!isNullPred(expr)) return expr;
    UPred pred = (UPred) expr;
    assert pred.args().size() == 1;

    if(pred.args().get(0).kind() != VAR) return expr;
    UVar targetVar = ((UVarTerm) pred.args().get(0)).var();

    if(!targetVar.is(UVar.VarKind.PROJ)) return expr;
    UName targetColName = targetVar.name();

    for(Constraint foreign : foreigns) {
      // check foreign whether exist
      if(foreign.columns().size() == foreign.refColumns().size() &&
              foreign.columns().size() == 1) {
        Column srcColumn = foreign.columns().get(0);
        Column tgtColumn = foreign.refColumns().get(0);
        // there exists a foreign key constraint, need to check whether target is unique
        if(Objects.equals(srcColumn.toString(), targetColName.toString())) {
          for(Constraint unique : primarys) {
            for(Column uniqueColumn : unique.columns()) {
              if(uniqueColumn == tgtColumn) { // it is primary!
                return UConst.zero();
              }
            }
          }
        }
      }

    }

    return expr;
  }

  /**  || sum{x, y, z}(R(x) * [a(x) = C] * T(y) * [a(y) = a(x)] ) ||
   *   = || sum{y, z}(T(y) * [a(y) = C] ) ||
   *   sum{y, z}(||sum{x}(R(x) * [a(x) = C] * T(y) * [a(y) = a(x)])||)
   *   = sum{y, z}(||(T(y) * [a(y) = C])||)
   *   a is primary key of R, and foreign key of T
   * */
  private UTerm applyForeignRemoveRedundantBoundVarInner(UTerm expr,
                                                         List<Constraint> primarys,
                                                         List<Constraint> foreigns,
                                                         Set<UVar> considerBoundVar) {
    final Set<UVar> newConsider = new HashSet<>(considerBoundVar);
    if (expr.kind() == SUMMATION)
      newConsider.addAll(((USum) expr).boundedVars());
    expr = transformSubTerms(expr, t -> applyForeignRemoveRedundantBoundVarInner(t, primarys, foreigns, newConsider));
    if (expr.kind() != SQUASH || expr.subTerms().get(0).kind() != SUMMATION) return expr;

    USum sum = (USum) ((USquash) expr).body();
    List<UTerm> subTerms = sum.body().subTerms();

    final Set<UVar> targetBoundeVar = considerBoundVar;
    targetBoundeVar.addAll(sum.boundedVars());

    for (Constraint foreign : foreigns) {
      if (foreign.columns().size() > 1) continue;
      //there should only exist one primary key related to this foreign key
      final Column srcCol = foreign.columns().get(0);
      final List<Constraint> tgtCons =  filter(primarys, t -> t.columns().size() == 1
              && Objects.equals(t.columns().get(0).name(), foreign.refColumns().get(0).name())
              && Objects.equals(t.columns().get(0).tableName(), foreign.refTable().name()));
      if (tgtCons.size() == 0) continue;
      final Column tgtCol = tgtCons.get(0).columns().get(0);
      final UName colName = UName.mk(srcCol.toString()), tableName = UName.mk(srcCol.tableName());
      final UName refColName = UName.mk(tgtCol.toString()), refTableName = UName.mk(tgtCol.tableName());
      for (UVar boundedVar : sum.boundedVars()) {
        final UTerm tableTerm =
                linearFind(subTerms, t -> t.equals(UTable.mk(refTableName, boundedVar)));
        final UVarTerm projVarTerm = UVarTerm.mk(UVar.mkProj(refColName, boundedVar));
        final Set<UVar> otherBoundedVars = new HashSet<>(filter(sum.boundedVars(), t -> !t.equals(boundedVar)));
        NaturalCongruence<UTerm> congruence = buildNaturalCongruence(subTerms);
        Set<UTerm> primaryKeysCongruence = congruence.eqClassOf(projVarTerm);
        UTerm constTerm = null;
        // check whether it satisfies R(x) * [a(x) = C]
        if (tableTerm == null
                || (constTerm = isEqVarConstantTerm(congruence, otherBoundedVars, projVarTerm)) == null) continue;
        // check whether it only contains like R(x) * [a(x) = C] * [a(y) = a(x)]
        if (!filter(subTerms, t -> t.isUsing(boundedVar)
                && !(t.equals(tableTerm)) // not R(x)
                && !(t.kind() == PRED // not [a(x) = C] or [a(y) = a(x)]
                  && ((UPred) t).isPredKind(EQ)
                  && t.isUsingProjVar(projVarTerm.var()))
        ).isEmpty()) continue;
        for (UVar otherBoundedVar : targetBoundeVar) {
          // only consider different boundedVar
          if (otherBoundedVar.equals(boundedVar)) continue;
          final UTerm tgtTableTerm =
                  linearFind(subTerms, t -> t.equals(UTable.mk(tableName, otherBoundedVar)));
          final UVarTerm tgtProjVarTerm = UVarTerm.mk(UVar.mkProj(colName, otherBoundedVar));
          if (tgtTableTerm == null || !primaryKeysCongruence.contains(tgtProjVarTerm)) continue;

          // modify here
          sum = (USum) sum.replaceAtomicTerm(projVarTerm, constTerm);
          sum.body().subTerms().removeAll(filter(subTerms, t -> t.isUsing(boundedVar)));
          sum.removeBoundedVar(boundedVar);
          isModified = true;
          return USquash.mk(sum);
        }
      }
    }
    return expr;
  }

  /**  || sum{x, y, z}(R(x) * [a(x) = C] * T(y) * [a(y) = a(x)] ) ||
   *   = || sum{y, z}(T(y) * [a(y) = C] ) ||
   *   sum{y, z}(||sum{x}(R(x) * [a(x) = C] * T(y) * [a(y) = a(x)])||)
   *   = sum{y, z}(||(T(y) * [a(y) = C])||)
   *   a is primary key of R, and foreign key of T
   * */
  public UTerm applyForeignRemoveRedundantBoundVar(UTerm expr, List<Constraint> primarys, List<Constraint> foreigns) {
    expr = applyForeignRemoveRedundantBoundVarInner(expr, primarys, foreigns, new HashSet<>());
    return expr;
  }

  /**
   * \sum_{t}(R(t) * ... * [R.a(t) = Constant]) ==> if a is unique, then  ||R(t')|| * ... * [R.a(t') = Constant]
   */
  private UTerm applyUniqueRemoveOneRecordSum(UTerm expr, List<Constraint> uniques) {
    expr = transformSubTerms(expr, t -> applyUniqueRemoveOneRecordSum(t, uniques));
    if (expr.kind() != SUMMATION) return expr;
    final USum summation = (USum) expr;
    final List<UTerm> subTerms = summation.body().subTerms();;
    final Map<UVar, List<UTerm>> removeVarTermMap = new HashMap<>();
    final Map<UVar, List<UTerm>> removeVarTableTermMap = new HashMap<>();

    for (Constraint unique : uniques) {
      if(unique.columns().size() != 1) continue;
      final Column column = unique.columns().get(0);
      final UName colName = UName.mk(column.toString()), tableName = UName.mk(column.tableName());
      for (UVar boundedVar : filter(summation.boundedVars(), v -> !removeVarTermMap.containsKey(v))) {
//            final UTerm tableTerm =
//                    linearFind(subTerms, t -> (!removeVarTermMap.containsKey(boundedVar)
//                            || !removeVarTermMap.get(boundedVar).contains(t))
//                            && t.equals(UTable.mk(tableName, boundedVar)));
        final List<UTerm> tableTerms = filter(subTerms, t -> (!removeVarTermMap.containsKey(boundedVar)
                || !removeVarTermMap.get(boundedVar).contains(t))
                && t.equals(UTable.mk(tableName, boundedVar)));
        final UVarTerm projVarTerm = UVarTerm.mk(UVar.mkProj(colName, boundedVar));
        final UTerm predTerm =
                linearFind(subTerms, t -> (!removeVarTermMap.containsKey(boundedVar)
                        || !removeVarTermMap.get(boundedVar).contains(t))
                        && isEqVarConstantTerm(t, projVarTerm));

        final List<UTerm> subSquashes = filter(subTerms, t -> t.kind() == SQUASH && t.isUsing(boundedVar));

        List<UTerm> squashTableTerms = new ArrayList<>();
        UTerm squashPredTerm = null;
        for(UTerm subSquashTerm : subSquashes) {
          List<UTerm> subSquashSubTerms = ((USquash) subSquashTerm).body().subTerms();
          squashTableTerms = filter(subSquashSubTerms, t -> (!removeVarTermMap.containsKey(boundedVar)
                  || !removeVarTermMap.get(boundedVar).contains(t))
                  && t.equals(UTable.mk(tableName, boundedVar)));
          squashPredTerm = linearFind(subSquashSubTerms, t -> (!removeVarTermMap.containsKey(boundedVar)
                  || !removeVarTermMap.get(boundedVar).contains(t))
                  && isEqVarConstantTerm(t, projVarTerm));

        }

        if (tableTerms.size() == 0 && squashTableTerms.size() == 0) continue;

        List<UTerm> toReplaceTerm = new ArrayList<>();
        toReplaceTerm.addAll(filter(subTerms, t -> t.isUsing(boundedVar)));
        if ((predTerm != null || squashPredTerm != null)) {
          removeVarTermMap.put(boundedVar, toReplaceTerm);
          tableTerms.addAll(squashTableTerms);
          removeVarTableTermMap.put(boundedVar, tableTerms);
        }
      }
    }

    for(Map.Entry<UVar, List<UTerm>> removeEntry : removeVarTermMap.entrySet()) {
      UVar repVar = removeEntry.getKey();
      List<UTerm> toReplaceTerms = removeEntry.getValue();
      if(!toReplaceTerms.isEmpty()){
        isModified = true;
        summation.body().subTerms().removeAll(toReplaceTerms);
        summation.removeBoundedVar(repVar);
        if(this.replaceVarOneRecord == null) {
          this.replaceVarOneRecord = mkFreshICRewriterBaseVar();
          icFreshVars.add(this.replaceVarOneRecord);
          translator.putTupleVarSchema(this.replaceVarOneRecord, translator.getTupleVarSchema(removeEntry.getKey()));
        }
        List<UTerm> newBodyList = new ArrayList<>();
        for(UTerm toReplaceTerm : toReplaceTerms) {
          if(toReplaceTerm.kind() == SQUASH) {
            List<UTerm> subSquashSubTerms = ((USquash) toReplaceTerm).body().subTerms();
            final List<UTerm> tableTerms = filter(subSquashSubTerms, t -> removeVarTableTermMap.get(repVar).contains(t));
            List<UTerm> squashTableTerms = new ArrayList<>();
            all(tableTerms, t -> squashTableTerms.add(USquash.mk(t)));
            ((USquash) toReplaceTerm).body().subTerms().removeAll(tableTerms);
            ((USquash) toReplaceTerm).body().subTerms().addAll(squashTableTerms);
          }
          toReplaceTerm.replaceVarInplace(repVar, this.replaceVarOneRecord, false);
          if(removeVarTableTermMap.get(repVar).contains(toReplaceTerm))
            newBodyList.add(USquash.mk(toReplaceTerm));
          else
            newBodyList.add(toReplaceTerm);
        }
        UMul newBody = UMul.mk(new ArrayList<>(newBodyList));
        summation.body().subTerms().add(newBody);
      }
    }


    return expr;
  }

  private UTerm isEqVarConstantTerm(NaturalCongruence<UTerm> congruence,
                                      Set<UVar> considerVars,
                                      UVarTerm targetTerm) {
    Set<UTerm> eqs = congruence.eqClassOf(targetTerm);
    List<UTerm> result = new ArrayList<>();
    for (final UTerm eq : eqs) {
      boolean isConsider = true;
      for(final UVar considerVar : considerVars) {
        if((eq.isUsing(considerVar) || eq.equals(targetTerm))) {
          isConsider = false;
          break;
        }
      }
      if(isConsider) result.add(eq);
    }

    if(result.isEmpty()) return null;
    return result.get(0);
  }

  private boolean isEqVarConstantTerm(UTerm pred, UVarTerm target) {
    // Check whether `pred` is like [a(t) = constant] for `target` a(t)
    if (pred.kind() != PRED || !((UPred) pred).isPredKind(EQ)) return false;

    assert ((UPred) pred).args().size() == 2;
    final UTerm predArg0 = ((UPred) pred).args().get(0), predArg1 = ((UPred) pred).args().get(1);
    if (!predArg0.equals(target) && !predArg1.equals(target)) return false;

    final UTerm otherTerm = predArg0.equals(target) ? predArg1 : predArg0;
    return otherTerm.kind() == CONST;
  }

  private boolean isEqVarFreeTerm(UTerm pred, UVarTerm target) {
    // Check whether `pred` is like [a(t) = e] for `target` a(t)
    if (pred.kind() != PRED || !((UPred) pred).isPredKind(EQ)) return false;

    assert ((UPred) pred).args().size() == 2;
    final UTerm predArg0 = ((UPred) pred).args().get(0), predArg1 = ((UPred) pred).args().get(1);
    if (!predArg0.equals(target) && !predArg1.equals(target)) return false;

    final UTerm otherTerm = predArg0.equals(target) ? predArg1 : predArg0;
    return all(UVar.getBaseVars(target.var()), v -> !otherTerm.isUsing(v));
  }

  private UTerm applyPrimaryNotNull(UTerm expr, List<Constraint> primaries) {
    expr = transformSubTerms(expr, t -> applyPrimaryNotNull(t, primaries));
    if (expr.kind() != MULTIPLY) return expr;

    final List<UTerm> predSubTerms = expr.subTermsOfKind(PRED);
    final Set<UVarTerm> notNullVarTerms = new HashSet<>();
    for (UTerm subTerm : predSubTerms) {
      final UPred pred = (UPred) subTerm;
      if (!pred.isBinaryPred()) continue;
      assert pred.args().size() == 2;
      final UTerm predArg0 = pred.args().get(0), predArg1 = pred.args().get(1);
      if (pred.isPredKind(EQ)) {
        if (predArg0.kind() == VAR && predArg1.kind() != VAR)
          notNullVarTerms.add((UVarTerm) predArg0);
        if (predArg0.kind() != VAR && predArg1.kind() == VAR) notNullVarTerms.add((UVarTerm) predArg1);
      } else {
        if (predArg0.kind() == VAR) notNullVarTerms.add((UVarTerm) predArg0);
        if (predArg1.kind() == VAR) notNullVarTerms.add((UVarTerm) predArg1);
      }
    }
    final NaturalCongruence<UVar> eqVarClass = getEqVarCongruenceInTermsOfMul(expr);
    final Set<UVarTerm> notNullVarTermsExtend = new HashSet<>(notNullVarTerms);
    final List<UTerm> notNullIgnoreTerms = new ArrayList<>();
    for (UVarTerm notNullVarTerm : notNullVarTerms) {
      final Set<UVar> eqVars = eqVarClass.eqClassOf(notNullVarTerm.var());
      notNullVarTermsExtend.addAll(map(eqVars, UVarTerm::mk));
    }
    for(UVarTerm notNullVarTerm : notNullVarTermsExtend) {
      notNullIgnoreTerms.add(UNeg.mk(mkIsNullPred(notNullVarTerm)));
    }

    final UTerm copy = expr.copy();
    final List<UTerm> newTableTerms = new ArrayList<>();
    final UMul mul = (UMul) expr;
    final List<UTerm> subTerms = mul.subTerms();
    for (Constraint primary : primaries) {
      final Column column = primary.columns().get(0);
      final UName colName = UName.mk(column.toString()), tableName = UName.mk(column.tableName());
      final List<UTerm> tables = filter(subTerms, t -> t.kind() == TABLE && ((UTable) t).tableName().equals(tableName));
      if(tables.isEmpty()) continue;
      for (UTerm table : tables) {
        newTableTerms.add(table);
        final UTable tab = (UTable) table;
        final UVar tbVar = tab.var();
        assert tbVar.kind() == UVar.VarKind.BASE;
        final UVar projVar = UVar.mkProj(colName, tbVar);
        final UTerm notNullTerm = (UTerm) UNeg.mk(mkIsNullPred(projVar));
        if (!subTerms.contains(notNullTerm) && !notNullIgnoreTerms.contains(notNullTerm)) {
          newTableTerms.add(notNullTerm);
          isModified = true;
        }
      }
    }

    if(!newTableTerms.isEmpty()) {
      subTerms.removeIf(t->t.kind() == TABLE && newTableTerms.contains(t));
      subTerms.addAll(newTableTerms);
    }

    return expr;
  }

  /**
   * PRIMARY a on exp
   * \sum{t}(exp(t) * [a(t) = CONSTANT] * ...) ==> exp(t) * [a(t) = CONSTANT] * ...
   */
  private UTerm rewritePrimary(UTerm expr) {
    final List<Constraint> primaries = new ArrayList<>();
    this.boundedStackVars.clear();
    if(selectedIC < 0) {
      for (Table table : schema.tables()) {
        table.constraints(ConstraintKind.PRIMARY).forEach(primaries::add);
      }
    } else {
      // select the selectedIC-th nonempty IC
      int nonemptyICIndex = 0;
      for (Table table : schema.tables()) {
        table.constraints(ConstraintKind.PRIMARY).forEach(primaries::add);
        if (!primaries.isEmpty() && nonemptyICIndex < selectedIC) {
          primaries.clear();
          nonemptyICIndex = nonemptyICIndex + 1;
        } else if (!primaries.isEmpty()) {
          break;
        }
      }
      hasIC = !primaries.isEmpty();
    }
    addUnboundedVar(expr);
    expr = removeUselessUnboundedPrimaryVar(expr, primaries, expr);
    return expr;
  }

  private void addUnboundedVar(UTerm expr) {
    if (expr.kind() == SUMMATION) {
      final USum summation = (USum) expr;
      final Set<UVar> boundedVars = summation.boundedVars();
      for(final UVar boundedVar : boundedVars)
        if(!this.boundedStackVars.contains(boundedVar))
          this.boundedStackVars.add(boundedVar);
    }
    for(final UTerm subTerm : expr.subTerms())
      addUnboundedVar(subTerm);
  }

  private UTerm removeUselessUnboundedPrimaryVar(UTerm expr, List<Constraint> primaries, UTerm ctx) {
    expr = transformSubTerms(expr, t -> removeUselessUnboundedPrimaryVar(t, primaries, ctx));
    if (expr.kind() != SUMMATION) return expr;

    final USum summation = (USum) expr;
    final Set<UVar> boundedVars = summation.boundedVars();
    final List<UTerm> tableSubTerms = summation.body().subTermsOfKind(TABLE);
    final List<UTerm> predSubTerms = summation.body().subTermsOfKind(PRED);

    // only consider one bounded var
    if (boundedVars.size() > 1) return expr;
    for (final UVar boundedVar : boundedVars) {
      // first it should have the table
      boolean tableConstraint = false;
      final List<UTerm> tableConstraintTerms = new ArrayList<>();
      UTerm predConstraintTerm = null;
      UName predColName = null;
      for (final UTerm tableTerm : tableSubTerms) {
        if (tableTerm.isUsing(boundedVar)) {
          tableConstraint = true;
          tableConstraintTerms.add(tableTerm);
        }
      }

      if(tableConstraint)
        assert(tableConstraintTerms.size() == 1);
      // second the primary key should equal to a constant
      boolean predConstraint = false;

      if(tableConstraint) {
        for (Constraint primary : primaries) {
          if (primary.columns().size() > 1){
            continue;
          }
          final Column column = primary.columns().get(0);
          final UName colName = UName.mk(column.toString()), tableName = UName.mk(column.tableName());
          final UVar projVar = UVar.mkProj(colName, boundedVar);

          if(!Objects.equals(((UTable) tableConstraintTerms.get(0)).tableName().toString(), tableName.toString()))
            continue;
          for (final UTerm predTerm : predSubTerms) {
            if(predTerm.isUsingProjVar(projVar)
                    && (predConstraintTerm = isPredTermUsingConstant((UPred)predTerm, summation)) != null) {
              predConstraint = true;
              predColName = colName;
              break;
            }
          }
        }
      }

      if (tableConstraint && predConstraint) {
        UVar newPrimaryVar = null;
        NaturalCongruence<UTerm> congruence = buildNaturalCongruence(List.of(ctx));
        Set<UTerm> primaryKeysCongruence = congruence.eqClassOf(predConstraintTerm);
        for(final UVar icFreshVar : icFreshVars) {
          UName tableName = ((UTable)tableConstraintTerms.get(0)).tableName();
          // only exist in the same table and primary key is the same
          // first check whether in the same table
          if(!UExprSupport.usesTableVar(ctx, tableName.toString(), boundedVar)
                  || !UExprSupport.usesTableVar(ctx, tableName.toString(), icFreshVar)) continue;
          // second check whether primary key is the same
          final UVar icProjVar = UVar.mkProj(predColName, icFreshVar);
          if(!primaryKeysCongruence.contains(UVarTerm.mk(icProjVar))) continue;
          newPrimaryVar = icFreshVar;
          break;
        }
        if(newPrimaryVar == null) {
          newPrimaryVar = mkFreshICRewriterBaseVar();
          icFreshVars.add(newPrimaryVar);
        }
        translator.putTupleVarSchema(newPrimaryVar, translator.getTupleVarSchema(boundedVar));
        summation.body().replaceVarInplace(boundedVar, newPrimaryVar, false);
        summation.removeBoundedVar(boundedVar);
        if(summation.boundedVars().isEmpty())
          expr = summation.body();
        isModified = true;
      }
    }

    return expr;
  }

  private UTerm isPredTermUsingConstant(UPred pred, USum summation) {
    if(!pred.isPredKind(EQ))
      return null;
    final Set<UVar> boundedVars = summation.boundedVars();
//        final List<UTerm> predSubTerms = expr.subTermsOfKind(PRED);
    final List<UTerm> args = pred.args();
    for(UTerm arg : args) {
      if(arg.kind() != VAR)
        return null;
    }
    final UVarTerm varTerm0 = (UVarTerm) args.get(0);
    final UVarTerm varTerm1 = (UVarTerm) args.get(1);
    final UVar baseVar0 = varTerm0.var().kind() == UVar.VarKind.PROJ ? varTerm0.var().args()[0]: varTerm0.var();
    final UVar baseVar1 = varTerm1.var().kind() == UVar.VarKind.PROJ ? varTerm1.var().args()[0]: varTerm1.var();
    if(!boundedVars.contains(baseVar0) || !boundedVars.contains(baseVar1)) {
      if(!((this.boundedStackVars.contains(baseVar0) && !summation.boundedVars().contains(baseVar0)) ||
              (this.boundedStackVars.contains(baseVar1) && !summation.boundedVars().contains(baseVar1))))
        return (summation.boundedVars().contains(baseVar0))? args.get(1): args.get(0);
      }
    return null;
  }

  private UTerm removeNotNullPred(UTerm expr, NaturalCongruence<UTerm> cong) {
    UPred pred = null;
    if (expr.kind() == NEGATION) {
      final UNeg neg = (UNeg) expr;
      if (neg.body().kind() != PRED) return expr;
      pred = (UPred) neg.body();
    } else if (expr.kind() == PRED) {
      pred = (UPred) expr;
    } else {
      return expr;
    }

    if (isNullPred(pred)) {
      if (pred.isTruePred(globalExpr) == 0) {
        isModified = true;
        return (expr.kind() == NEGATION) ? UConst.one() : UConst.zero();
      }
      Set<UTerm> eqTuples = cong.eqClassOf(pred.args().get(0));
      if (any(eqTuples, t -> {
        ArrayList<UTerm> args = new ArrayList<>();
        args.add(t);
        UPred tmpPred = UPred.mk(UPred.PredKind.FUNC, UName.NAME_IS_NULL, args);
        return tmpPred.isTruePred(globalExpr) == 0;
      })) {
        isModified = true;
        return (expr.kind() == NEGATION) ? UConst.one() : UConst.zero();
      }
    }
    return expr;
  }

  private UTerm removeNotNull(UTerm expr) {
    expr = transformSubTerms(expr, t -> removeNotNull(t));
    switch (expr.kind()) {
      case SUMMATION: {
        USum summation = (USum) expr;
        Set<UVar> boundedVars = summation.boundedVars();
        List<UTerm> subTerms = summation.body().subTerms();
        NaturalCongruence<UTerm> cong = buildNaturalCongruence(subTerms);
        for (int i = 0; i < subTerms.size(); ++i) {
          subTerms.set(i, removeNotNullPred(subTerms.get(i), cong));
        }
        return USum.mk(boundedVars, UMul.mk(subTerms));
      }
      default: {
        return removeNotNullPred(expr, NaturalCongruence.mk());
      }
    }
  }
}

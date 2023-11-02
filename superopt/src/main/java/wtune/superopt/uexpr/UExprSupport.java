package wtune.superopt.uexpr;

import wtune.common.utils.NaturalCongruence;
import wtune.sql.ast.ExprFields;
import wtune.sql.ast.SqlNode;
import wtune.sql.ast.constants.LiteralKind;
import wtune.sql.plan.Expression;
import wtune.sql.plan.PlanContext;
import wtune.sql.schema.Schema;
import wtune.superopt.substitution.Substitution;
import wtune.superopt.substitution.SubstitutionTranslatorResult;
import wtune.superopt.uexpr.normalizer.UExprPreprocessor;
import wtune.superopt.uexpr.normalizer.UNormalization;
import wtune.superopt.uexpr.normalizer.UNormalizationEnhance;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

import static wtune.common.utils.Commons.coalesce;
import static wtune.common.utils.IterableSupport.all;
import static wtune.sql.ast.ExprKind.*;
import static wtune.sql.plan.PlanSupport.colIsNullPredicate;
import static wtune.sql.plan.PlanSupport.isSimpleIntArithmeticExpr;
import static wtune.superopt.uexpr.UKind.*;
import static wtune.superopt.uexpr.UName.NAME_IS_NULL;

public abstract class UExprSupport {

  // Used flag bits (the most significant bit is on the left):
  // (31-24) _ _ _ _ _ _ _ _
  // (23-16) _ _ _ _ _ _ _ _
  // (15-08) _ _ _ _ _ _ _ _
  // (07-01) _ _ _ x x x x x
  // ("_" are unused, while "x" are used)

  public static final int UEXPR_FLAG_SUPPORT_DEPENDENT_SUBQUERY = 1;
  public static final int UEXPR_FLAG_CHECK_SCHEMA_FEASIBLE = 1 << 1;

  public static final int UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE = 1 << 2;

  // Below are used for concrete plan -> template translation issues
  public static final int UEXPR_FLAG_VERIFY_CONCRETE_PLAN = 1 << 3;

  // decide how to translate predicates like "x IN (a, b, ...)"
  public static final int UEXPR_FLAG_NO_EXPLAIN_PREDICATES = 1 << 4;

  private UExprSupport() {}

  public static List<UTerm> copyTermList(List<UTerm> exprList) {
    final List<UTerm> copiedList = new ArrayList<>(exprList.size());
    for (UTerm expr : exprList) copiedList.add(expr.copy());

    return copiedList;
  }

  public static boolean isCriticalValue(UTerm subTerm, UTerm expr) {
    // Check whether: subTerm = 0 infers expr = 0
    final UTerm copy = expr.copy();
    final UTerm reduced = copy.replaceAtomicTerm(subTerm, UConst.zero());
    return UExprSupport.normalizeExpr(reduced).equals(UConst.ZERO);
  }

  public static boolean usesTableVar(UTerm expr, String tableName, UVar var) {
    if (expr instanceof UTable table) {
      return table.tableName().toString().equals(tableName)
              && table.var().equals(var);
    } else {
      // recursion
      for (UTerm term : expr.subTerms()) {
        if (usesTableVar(term, tableName, var)) return true;
      }
      return false;
    }
  }

  @Deprecated
  public static UTerm mkBinaryArithmeticPred(Expression expr, UVar var) {
    assert isSimpleIntArithmeticExpr(expr);
    return mkBinaryArithmeticPred0(expr.template(), var);
  }

  private static UTerm mkBinaryArithmeticPred0(SqlNode node, UVar var) {
    if (ColRef.isInstance(node)) return UVarTerm.mk(var.copy());
    if (Literal.isInstance(node)) {
      if (node.$(ExprFields.Literal_Kind) == LiteralKind.INTEGER) {
        final Integer value = (Integer) node.$(ExprFields.Literal_Value);
        return UConst.mk(value);
      }
      else return null;
    }

    if (Unary.isInstance(node)) {
      final UTerm lhs = mkBinaryArithmeticPred0(node.$(ExprFields.Unary_Expr), var);
      if (lhs == null) return null;
      switch (node.$(ExprFields.Unary_Op)) {
        case NOT: return UNeg.mk(lhs);
        default:
          throw new IllegalArgumentException("Unsupported binary operator: " + node.$(ExprFields.Unary_Op));
      }
    }

    if (Binary.isInstance(node)) {
      final UTerm lhs = mkBinaryArithmeticPred0(node.$(ExprFields.Binary_Left), var);
      final UTerm rhs = mkBinaryArithmeticPred0(node.$(ExprFields.Binary_Right), var);
      if (colIsNullPredicate(node)) {
        // `WHERE col IS NULL`
        assert lhs != null && lhs.kind() == VAR;
        return mkIsNullPred((UVarTerm) lhs);
      }

      if (lhs == null || rhs == null) return null;

      switch (node.$(ExprFields.Binary_Op)) {
        // Logic operators
        case AND: return UMul.mk(lhs, rhs);
        case OR: return USquash.mk(UAdd.mk(lhs, rhs));
        // Comparison operators
        case EQUAL: return UPred.mkBinary(UPred.PredKind.EQ, lhs, rhs);
        case NOT_EQUAL: return UPred.mkBinary(UPred.PredKind.NEQ, lhs, rhs);
        case LESS_THAN : return UPred.mkBinary(UPred.PredKind.LT, lhs, rhs);
        case LESS_OR_EQUAL: return UPred.mkBinary(UPred.PredKind.LE, lhs, rhs);
        case GREATER_THAN: return UPred.mkBinary(UPred.PredKind.GT, lhs, rhs);
        case GREATER_OR_EQUAL: return UPred.mkBinary(UPred.PredKind.GE, lhs, rhs);
        // Arithmetic operators
        case PLUS: return UAdd.mk(lhs, rhs);
        case MULT: return UMul.mk(lhs, rhs);
        case DIV:
          if (lhs.kind() == CONST && rhs.kind() == CONST) {
            final Integer lhsV = ((UConst) lhs).value(), rhsV = ((UConst) rhs).value();
            if (rhsV * (lhsV / rhsV) == lhsV) return UConst.mk(lhsV / rhsV);
          }
          throw new IllegalArgumentException("Unsupported binary operator: " + node.$(ExprFields.Binary_Op));
        default:
          throw new IllegalArgumentException("Unsupported binary operator: " + node.$(ExprFields.Binary_Op));
      }
    }

    assert false : "Should be a single-param arithmetic Expression";
    return null;
  }

  /**
   * Null predicate related functions
   */
  public static UTerm mkNotNullPred(UVar var) {
    return UNeg.mk(mkIsNullPred(var));
  }

  public static UTerm mkIsNullPred(UVar var) {
    return UPred.mkFunc(NAME_IS_NULL, var);
  }

  public static UTerm mkNotNullPred(UTerm var) {
    return UNeg.mk(mkIsNullPred(var));
  }

  public static UTerm mkIsNullPred(UTerm var) {
    return UPred.mkFunc(NAME_IS_NULL, var);
  }

  public static boolean varIsNotNullPred(UTerm expr) {
    if (expr.kind() != NEGATION) return false;
    final UTerm body = ((UNeg) expr).body();
    return varIsNullPred(body);
  }

  public static boolean varIsNullPred(UTerm expr) {
    if (expr.kind() != PRED) return false;

    final UPred pred = (UPred) expr;
    if (pred.isPredKind(UPred.PredKind.FUNC) && NAME_IS_NULL.equals(pred.predName())) {
      assert pred.args().size() == 1;
      return pred.args().get(0).kind().isVarTerm();
    }
    return false;
  }

  public static boolean isNotNullPred(UTerm expr) {
    if (expr.kind() != NEGATION) return false;
    final UTerm body = ((UNeg) expr).body();
    return isNullPred(body);
  }

  public static boolean isNullPred(UTerm expr) {
    if (expr.kind() != PRED) return false;

    final UPred pred = (UPred) expr;
    if (pred.isPredKind(UPred.PredKind.FUNC) && NAME_IS_NULL.equals(pred.predName())) {
      assert pred.args().size() == 1;
      return true;
    }
    return false;
  }

  // expr can be a new UTerm after replacing nullvar in it with NULL
  public static boolean canReplaceNullVar(UTerm expr, UVar nullVar) {
    if (!expr.isUsing(nullVar))
      return true;
    switch (expr.kind()) {
      case NEGATION: {
        return canReplaceNullVar(((UNeg)expr).body(), nullVar);
      }
      case SQUASH: {
        return canReplaceNullVar(((USquash)expr).body(), nullVar);
      }
      case MULTIPLY:
      case ADD: {
        for(UTerm subterm : expr.subTerms()) {
          if (!canReplaceNullVar(subterm, nullVar)) {
            return false;
          }
        }
        return true;
      }
      case PRED: {
        return canReplaceNullVarPred((UPred) expr, nullVar);
      }
      case VAR: {
        return expr.isUsing(nullVar);
      }
      default: {
        return false;
      }
    }
  }

  public static UTerm afterReplaceNullVar(UTerm expr, UVar nullVar) {
    if (!expr.isUsing(nullVar))
      return expr;
    switch (expr.kind()) {
      case NEGATION: {
        UTerm newBody = afterReplaceNullVar(((UNeg)expr).body(), nullVar);
        if (newBody == null) {
          return null;
        } else if (newBody instanceof UConst) {
          int val = ((UConst) newBody).value();
          return (val == 0) ? UConst.one() : UConst.zero();
        } else {
          return UNeg.mk(newBody);
        }
      }
      case SQUASH: {
        UTerm newBody = afterReplaceNullVar(((USquash)expr).body(), nullVar);
        if (newBody == null) {
          return null;
        } else if (newBody instanceof UConst) {
          int val = ((UConst) newBody).value();
          return (val == 0) ? UConst.zero() : UConst.one();
        } else {
          return USquash.mk(newBody);
        }
      }
      case MULTIPLY:
      case ADD: {
        ArrayList<UTerm> newSubTerms = new ArrayList<>();
        for(UTerm subterm : expr.subTerms()) {
          UTerm newSubTerm = afterReplaceNullVar(subterm, nullVar);
          if (newSubTerm == null)
            return null;
          newSubTerms.add(newSubTerm);
        }
        return (expr.kind() == MULTIPLY) ? UMul.mk(newSubTerms) : UAdd.mk(newSubTerms);
      }
      case PRED: {
        return afterReplaceNullVarPred((UPred) expr, nullVar);
      }
      case VAR: {
        return null;
      }
      default: {
        return expr;
      }
    }
  }

  public static boolean canReplaceNullVarPred(UPred pred, UVar nullVar) {
    switch (pred.predKind()) {
      case FUNC: {
        return isNullPred(pred);
      }
      case EQ: case GE: case GT: case LE: case LT: {
        assert pred.args().size() == 2;
        UTerm left = pred.args().get(0);
        UTerm right = pred.args().get(1);
        if (canReplaceNullVar(left, nullVar) && canReplaceNullVar(right, nullVar)) {
          return true;
        } else if (left instanceof UVarTerm && left.isUsing(nullVar) && right instanceof UConst) {
          return true;
        } else if (left instanceof UConst && right instanceof UVarTerm && right.isUsing(nullVar)) {
          return true;
        } else {
          return false;
        }
      }
      default: {
        return false;
      }
    }
  }

  public static UTerm afterReplaceNullVarCmpPred(UTerm left, UTerm right, UPred.PredKind kind) {
    switch (kind) {
      case EQ: {
        if (left == null && right == null) {
          return UConst.one();
        } else if (left == null) {
          if (right instanceof UConst) {
            return UConst.zero();
          }
          if(right instanceof UVarTerm) {
            ArrayList<UTerm> args = new ArrayList<>();
            args.add(right);
            return UPred.mk(UPred.PredKind.FUNC, NAME_IS_NULL, args);
          }
          return null;
        } else if (right == null) {
          if (left instanceof UConst) {
            return UConst.zero();
          }
          if(left instanceof UVarTerm) {
            ArrayList<UTerm> args = new ArrayList<>();
            args.add(left);
            return UPred.mk(UPred.PredKind.FUNC, NAME_IS_NULL, args);
          }
          return null;
        } else {
          return null;
        }
      }
      case LT: case GT: {
        if (left == null && right == null) {
          return UConst.zero();
        } else if (left == null || right == null) {
          return UConst.zero();
        } else {
          return null;
        }
      }
      default: {
        return null;
      }
    }
  }

  public static UTerm afterReplaceNullVarPred(UPred pred, UVar nullVar) {
    UPred.PredKind kind = pred.predKind();
    switch (kind) {
      case FUNC: {
        assert isNullPred(pred);
        return UConst.one();
      }
      case EQ: case GE: case GT: case LE: case LT: {
        assert pred.args().size() == 2;
        UTerm left = pred.args().get(0);
        UTerm right = pred.args().get(1);
        if (canReplaceNullVar(left, nullVar) && canReplaceNullVar(right, nullVar)) {
          UTerm leftVal = afterReplaceNullVar(left, nullVar);
          UTerm rightVal = afterReplaceNullVar(right, nullVar);
          UTerm newPred = afterReplaceNullVarCmpPred(leftVal, rightVal, kind);
          return newPred == null ? pred : newPred;
        } else if (left instanceof UVarTerm && left.isUsing(nullVar) && right instanceof UConst) {
          return UConst.zero();
        } else if (left instanceof UConst && right instanceof UVarTerm && right.isUsing(nullVar)) {
          return UConst.zero();
        } else {
          return pred;
        }
      }
      default: {
        return pred;
      }
    }
  }


  public static UVar getIsNullPredVar(UPred pred) {
    assert varIsNullPred(pred);
    final UTerm nullArg = pred.args().get(0);
    return ((UVarTerm) nullArg).var();
  }

  public static boolean isPredOfVarStringArg(UPred pred) {
    // check whether arguments of this pred are UVarTerms
    // i.e. check whether this pred only takes tuple Vars as input
    final List<UTerm> args = pred.args();
    return all(args, arg -> arg.kind().isVarTerm() || arg.kind() == STRING);
  }

  public static boolean isPredOfVarConstArg(UPred pred) {
    // check whether arguments of this pred are UVarTerms
    // i.e. check whether this pred only takes tuple Vars as input
    final List<UTerm> args = pred.args();
    return all(args, arg -> arg.kind().isVarTerm() || arg.kind() == CONST);
  }

  public static boolean isPredOfVarArg(UPred pred) {
    // check whether arguments of this pred are UVarTerms
    // i.e. check whether this pred only takes tuple Vars as input
    final List<UTerm> args = pred.args();
    return all(args, arg -> arg.kind().isVarTerm());
  }

  public static List<UVar> getPredVarArgs(UPred pred) {
    assert isPredOfVarArg(pred);
    final List<UTerm> args = pred.args();
    final List<UVar> varArgs = new ArrayList<>(args.size());
    for (UTerm arg : args) {
      varArgs.add(((UVarTerm) arg).var());
    }
    return varArgs;
  }

  /**
   * eq tuple vars congruence searching functions
   */
  // Get equivalent UVars in a UMul's sub-terms, e.g. `[a0(t0) = a1(t1)]` -> eq class {`a0(t0)`, `a1(t1)`}
  public static NaturalCongruence<UVar> getEqVarCongruenceInTermsOfMul(UTerm mulContext) {
    assert mulContext.kind() == MULTIPLY;
    final NaturalCongruence<UVar> varEqClass = NaturalCongruence.mk();
    for (UTerm subTerm : mulContext.subTermsOfKind(PRED)) {
      final UPred pred = (UPred) subTerm;
      if (pred.isPredKind(UPred.PredKind.EQ) && isPredOfVarArg(pred)) {
        final List<UVar> eqPredVars = getPredVarArgs(pred);
        assert eqPredVars.size() == 2;
        final UVar varArg0 = eqPredVars.get(0), varArg1 = eqPredVars.get(1);
        varEqClass.putCongruent(varArg0, varArg1);
      }
    }
    return varEqClass;
  }

  /** Get equivalent UVars/UStrings in a UMul's sub-terms
   *  e.g. `[a0(t0) = a1(t1)]` -> eq class {`a0(t0)`, `a1(t1)`}
   *  e.g. `[a0(t0) = 'a']` -> eq class {`a0(t0)`, 'a'}
   * */
  public static NaturalCongruence<UTerm> getEqVarStringCongruenceInTermsOfMul(UTerm mulContext) {
    return getEqCongruenceInTermsOfMul(mulContext, UExprSupport::isPredOfVarStringArg);
  }

  /** Get equivalent UVars/UConsts in a UMul's sub-terms
   *  e.g. `[a0(t0) = a1(t1)]` -> eq class {`a0(t0)`, `a1(t1)`}
   *  e.g. `[a0(t0) = 10]` -> eq class {`a0(t0)`, 10}
   * */
  public static NaturalCongruence<UTerm> getEqVarConstCongruenceInTermsOfMul(UTerm mulContext) {
    return getEqCongruenceInTermsOfMul(mulContext, UExprSupport::isPredOfVarConstArg);
  }

  /** Get equivalent UVars/UConsts in a UMul's sub-terms
   *  e.g. `[a0(t0) = a1(t1)]` -> eq class {`a0(t0)`, `a1(t1)`}
   *  e.g. `[a0(t0) = 10]` -> eq class {`a0(t0)`, 10}
   *  NOTE: this function only consider critical value for ctx!
   * */
  public static NaturalCongruence<UTerm> getEqVarConstCongruenceInTermsOfMulCritical(UTerm mulContext, UTerm ctx) {
    return getEqCongruenceInTermsOfMul(mulContext, pred -> isPredOfVarConstArg(pred) && isCriticalValue(pred, ctx));
  }

  /** Get equivalent UTerms in a UMul's sub-terms based on EQ predicates.
   *  The specified filter ignores sub-terms that make it return false.
   * */
  public static NaturalCongruence<UTerm> getEqCongruenceInTermsOfMul(UTerm mulContext, Function<UPred, Boolean> filter) {
    assert mulContext.kind() == MULTIPLY;
    final NaturalCongruence<UTerm> varEqClass = NaturalCongruence.mk();
    for (UTerm subTerm : mulContext.subTermsOfKind(PRED)) {
      final UPred pred = (UPred) subTerm;
      if (pred.isPredKind(UPred.PredKind.EQ) && filter.apply(pred)) {
        final List<UTerm> eqPredTerms = pred.args();
        assert eqPredTerms.size() == 2;
        final UTerm termArg0 = eqPredTerms.get(0), termArg1 = eqPredTerms.get(1);
        varEqClass.putCongruent(termArg0, termArg1);
      }
    }
    return varEqClass;
  }

  // Get equivalent UVars in a UMul's sub-terms, e.g. `[a0(t0) = a1(t1)]` -> eq class {`a0(t0)`, `a1(t1)`}
  public static void getEqVarCongruenceInTermsOfMul(NaturalCongruence<UVar> varEqClass, UTerm mulContext) {
    assert mulContext.kind() == MULTIPLY;
    for (UTerm subTerm : mulContext.subTermsOfKind(PRED)) {
      final UPred pred = (UPred) subTerm;
      if (pred.isPredKind(UPred.PredKind.EQ) && isPredOfVarArg(pred)) {
        final List<UVar> eqPredVars = getPredVarArgs(pred);
        assert eqPredVars.size() == 2;
        final UVar varArg0 = eqPredVars.get(0), varArg1 = eqPredVars.get(1);
        varEqClass.putCongruent(varArg0, varArg1);
      }
    }
  }

  public static void getEqVarCongruenceInTermsOfPred(NaturalCongruence<UVarTerm> varEqClass, UTerm predContext) {
    assert predContext.kind() == PRED && ((UPred) predContext).isPredKind(UPred.PredKind.EQ);
    final UPred pred = (UPred) predContext;
    if (pred.isPredKind(UPred.PredKind.EQ)) {
      final List<UTerm> eqPredVars = pred.args();
      assert eqPredVars.size() == 2;
      final UTerm varArg0 = eqPredVars.get(0), varArg1 = eqPredVars.get(1);
      if (varArg0 instanceof UVarTerm && varArg1 instanceof UVarTerm)
        varEqClass.putCongruent((UVarTerm) varArg0, (UVarTerm) varArg1);
    }
  }

  // Get equivalent UVars from anywhere of a UTerm (used to find UVars of equivalent schemas and do normalizations)
  public static NaturalCongruence<UVar> getSchemaEqVarCongruence(UTerm expr) {
    final NaturalCongruence<UVar> varEqClass = NaturalCongruence.mk();
    getSchemaEqVarCongruence0(expr, varEqClass);
    return varEqClass;
  }

  private static void getSchemaEqVarCongruence0(UTerm expr, NaturalCongruence<UVar> varEqClass) {
    if (expr.kind() == PRED) {
      final UPred pred = (UPred) expr;
      if (pred.isPredKind(UPred.PredKind.EQ) && isPredOfVarArg(pred)) {
        final List<UVar> eqPredArgs = getPredVarArgs(pred);
        assert eqPredArgs.size() == 2;
        final UVar varArg0 = eqPredArgs.get(0), varArg1 = eqPredArgs.get(1);
        varEqClass.putCongruent(varArg0, varArg1);
      }
    }
    for (UTerm subTerm : expr.subTerms()) getSchemaEqVarCongruence0(subTerm, varEqClass);
  }

  /** Reason about pre-defined functions (e.g. like_op) */
  public static UTerm preprocessExpr(UTerm expr) {
    return new UExprPreprocessor().preprocess(expr);
  }

  /**
   * U-expression normalization functions
   */
  public static UTerm normalizeExpr(UTerm expr) {
    return new UNormalization(expr).normalizeTerm();
  }

  public static UTerm normalizeExprEnhance(UTerm expr) {
    return new UNormalizationEnhance(expr).normalizeTerm();
  }

  static boolean checkNormalForm(UTerm expr) {
    return UNormalization.isNormalForm(expr);
  }

  /**
   * Apply transformation to each term in `terms`.
   *
   * <p>Returns the original `terms` if each term are not changed (or changed in-place). Otherwise,
   * a new list.
   */
  static List<UTerm> transformTerms(List<UTerm> terms, Function<UTerm, UTerm> transformation) {
    List<UTerm> copies = null;
    for (int i = 0, bound = terms.size(); i < bound; i++) {
      final UTerm subTerm = terms.get(i);
      final UTerm modifiedSubTerm = transformation.apply(subTerm);
      if (modifiedSubTerm != subTerm) {
        if (copies == null) copies = new ArrayList<>(terms);
        copies.set(i, modifiedSubTerm);
      }
    }

    return coalesce(copies, terms);
  }

  static UTerm remakeTerm(UTerm template, List<UTerm> subTerms) {
    if (subTerms == template.subTerms()) return template;

    // should not reach here by design
    return switch (template.kind()) {
      case CONST, TABLE, VAR, STRING -> template;
      case PRED -> UPred.mk(((UPred) template).predKind(), ((UPred) template).predName(), subTerms);
      case FUNC -> UFunc.mk(((UFunc) template).funcKind(), ((UFunc) template).funcName(), subTerms);
      case ADD -> UAdd.mk(subTerms);
      case MULTIPLY -> UMul.mk(subTerms);
      case NEGATION -> UNeg.mk(subTerms.get(0));
      case SQUASH -> USquash.mk(subTerms.get(0));
      case SUMMATION -> USum.mk(((USum) template).boundedVars(), subTerms.get(0));
    };
  }

  /**
   * Apply transformation to each sub term of `term`.
   *
   * <p>Returns the original `terms` if each term are not changed (or changed in-place). Otherwise,
   * a new list.
   */
  public static UTerm transformSubTerms(UTerm expr, Function<UTerm, UTerm> transformation) {
    return remakeTerm(expr, transformTerms(expr.subTerms(), transformation));
  }

  /**
   * Functions to get translated U-exprs
   */
  public static UExprTranslationResult translateToUExpr(Substitution rule) {
    return new UExprTranslator(rule, 0, null).translate();
  }

  public static UExprTranslationResult translateToUExpr(Substitution rule, int tweaks) {
    return new UExprTranslator(rule, tweaks, null).translate();
  }

  public static UExprTranslationResult translateToUExpr
      (Substitution rule, int tweaks, SubstitutionTranslatorResult extraInfo) {
    return new UExprTranslator(rule, tweaks, extraInfo).translate();
  }

  public static UExprConcreteTranslationResult translateQueryWithVALUESToUExpr
      (String sql0, String sql1, Schema baseSchema, int tweaks) {
    // Process query with `VALUES` feature
    return new UExprConcreteTranslator(sql0, sql1, baseSchema, tweaks).translate();
  }

  public static UExprConcreteTranslationResult translateQueryToUExpr
      (PlanContext plan0, PlanContext plan1, int tweaks) {
    // Process concrete queries translation
    return new UExprConcreteTranslator(plan0, plan1, tweaks).translate();
  }
}

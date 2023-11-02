package wtune.superopt.uexpr.normalizer;

import wtune.common.utils.NaturalCongruence;
import wtune.sql.plan.Value;
import wtune.sql.schema.Schema;
import wtune.sql.schema.Table;
import wtune.superopt.liastar.Liastar;
import wtune.superopt.logic.CASTSupport;
import wtune.superopt.uexpr.*;

import java.util.*;
import java.util.stream.Collectors;

import static wtune.common.utils.IterableSupport.*;
import static wtune.common.utils.ListSupport.*;
import static wtune.superopt.uexpr.UExprSupport.*;
import static wtune.superopt.uexpr.UKind.*;
import static wtune.superopt.uexpr.UKind.VAR;
import static wtune.superopt.uexpr.UExprConcreteTranslator.QueryTranslator.globalExpr;
import static wtune.superopt.uexpr.UPred.PredKind.*;

public class QueryUExprNormalizer extends UNormalization {
  private Schema schema;

  private final List<UVar> icFreshVars;

  private final UExprConcreteTranslator.QueryTranslator translator;

  public QueryUExprNormalizer(UTerm expr, Schema schema, UExprConcreteTranslator.QueryTranslator translator) {
    super(expr);
    this.schema = schema;
    this.translator = translator;
    this.icFreshVars = new ArrayList<>();
  }

  public QueryUExprNormalizer(UTerm expr, Schema schema, UExprConcreteTranslator.QueryTranslator translator, List<UVar> icFreshVars) {
    super(expr);
    this.schema = schema;
    this.translator = translator;
    this.icFreshVars = icFreshVars;
  }

  static String preUexpr = null;
  static boolean preIsMod = false;


  public UTerm commonNormalizeTerm() {
    expr = performNormalizeRule(this::removeUselessAttrSym);
    expr = performNormalizeRule(this::extractorPreprocess);
    expr = performNormalizeRule(this::extractUnrelatedSumTerms);
    expr = performNormalizeRule(this::removeUselessNegSumWithSameFilter);
    expr = performNormalizeRule(this::simplifySummations);
    expr = performNormalizeRule(this::transformSumUnrelatedTermsEQPred);
    expr = performNormalizeRule(this::removeNullMultiplication);
//    expr = performNormalizeRule(this::extractUnrelatedSumSubTerms);
    return expr;
  }

  ArrayList<UTerm> notNullTerms = new ArrayList<>();

  @Override
  public UTerm normalizeTerm() {
    notNullTerms.clear();
    detectNotNullTuples(expr);
    do {
      expr = super.normalizeTerm();
      UExprConcreteTranslator.QueryTranslator.globalExpr = expr;
      isModified = false;
      expr = performNormalizeRule(this::removeUselessBoundedVar);
      expr = performNormalizeRule(this::removeUselessBoundedVarsNestedly);
      expr = performNormalizeRule(this::propagateNullBoundedVar);
      expr = performNormalizeRule(this::removeUselessInferenceBoundedVar);
      expr = performNormalizeRule(this::removeIsNullPredOnValue);
      expr = performNormalizeRule(this::inferIsNullPredResult);
      expr = performNormalizeRule(this::removeUselessAggBoundedVar);
      expr = performNormalizeRule(this::removeUselessSquashSumFromSumBody);
      expr = performNormalizeRule(this::removeUselessSumWithNegation);
      expr = performNormalizeRule(this::removeUselessNegSumWithSameFilter);
      expr = performNormalizeRule(this::removeUselessSquashNegDupSum);
      expr = performNormalizeRule(this::simplifyUniqueMaxMin);
      expr = performNormalizeRule(this::replaceUselessNegSumWithNumber);
      expr = performNormalizeRule(this::removeDupSubTerm);
      expr = performNormalizeRule(this::removeSumEqPred);
      expr = performNormalizeRule(this::autoTypeConversion);
      expr = performNormalizeRule(this::eqNullConversion);
    } while (isModified);
    return expr;
  }

  public UTerm normalizeTermRegroup(Set<UVar> boundVarSet) {
    do {
      isModified = false;
      expr = renameSameBoundedVarSummation(expr, boundVarSet);
    } while (isModified);
    return expr;
  }

  /** Rename all the vars between different summation if their boundedVars have same name
   *  e.g. sum{t1} + sum{t1} => sum{t1} + sum{t2}     t1 and t2 have the same schema
   */
  private UTerm renameSameBoundedVarSummation(UTerm expr, Set<UVar> varSet) {
    for (UTerm subTerm : expr.subTerms())
      renameSameBoundedVarSummation(subTerm, varSet);
    final UKind kind = expr.kind();
    if (kind != SUMMATION) return expr;

    final USum sum = (USum) expr;
    final Set<UVar> boundedVars = sum.boundedVars();
    final HashMap<UVar, UVar> replaceMap = new HashMap<>();

    for (final UVar boundedVar : boundedVars) {
      assert boundedVar.kind() == UVar.VarKind.BASE;
      if (varSet.contains(boundedVar)) {
        final UVar newVar = translator.mkFreshBaseVar();
        translator.putTupleVarSchema(newVar, translator.getTupleVarSchema(boundedVar));
        varSet.add(newVar);
        replaceMap.put(boundedVar, newVar);
      } else {
        varSet.add(boundedVar);
      }
    }


    for (final Map.Entry<UVar, UVar> entry : replaceMap.entrySet()) {
      sum.replaceVarInplace(entry.getKey(), entry.getValue(), true);
    }

    return expr;
  }

  public void detectNotNullTuples(UTerm expr) {
    switch (expr.kind()) {
      case MULTIPLY:
      case ADD:
      case NEGATION:
      case SQUASH:
      case FUNC:
      case SUMMATION: {
        for (UTerm t : expr.subTerms()) {
          detectNotNullTuples(t);
        }
        return;
      }
      case STRING: case VAR: case TABLE: case CONST: {
        return;
      }
      case PRED: {
        UPred pred = (UPred) expr;
        switch (pred.predKind()) {
          case LE: case LT: case GT: case GE: case EQ: {
            UTerm op0 = pred.args().get(0);
            UTerm op1 = pred.args().get(1);
            if (op0.kind() == VAR && op1.kind() == SUMMATION)
              notNullTerms.add(op0);
            else if (op1.kind() == VAR && op0.kind() == SUMMATION)
              notNullTerms.add(op1);
          }
          default: return;
        }
      }
      default: {
        System.out.println("Unsupported type of U-expressions !!!");
        assert false;
      }
    }
  }

  // TODO: need to consider non-const boundedVar,∑{x, y} means y is a CONST to x
  public static UTerm searchEQConstProjVar(UVar projVar, List<UTerm> termList, Set<UVar> boundedVars) {
    for (final UTerm term : termList) {
      if (term instanceof UPred pred) {
        if (pred.isPredKind(EQ)) {
          List<UTerm> args = pred.args();
          assert args.size() == 2;
          if (args.get(0).kind() == VAR && args.get(0).isUsingProjVar(projVar)) {
            boolean select = true;
            for (UVar boundedVar : boundedVars)
              if (args.get(1).isUsing(boundedVar)) select = false;
            if (select) return args.get(1);
          }
          if (args.get(1).kind() == VAR && args.get(1).isUsingProjVar(projVar)) {
            boolean select = true;
            for (UVar boundedVar : boundedVars)
              if (args.get(0).isUsing(boundedVar)) select = false;
            if (select) return args.get(0);
          }
        }
      }
    }
    return null;
  }

  public static void buildNaturalCongruenceRecursively(List<UTerm> terms, NaturalCongruence<UTerm> result) {
    for (UTerm term : terms) {
      switch (term.kind()) {
        case PRED: {
          UPred pred = (UPred) term;
          if (!pred.isPredKind(EQ)) continue;
          result.putCongruent(pred.args().get(0), pred.args().get(1));
          break;
        }
        case SQUASH: {
          buildNaturalCongruenceRecursively(((USquash) term).body().subTerms(), result);
          break;
        }
        case SUMMATION: {
          buildNaturalCongruenceRecursively(((USum) term).body().subTerms(), result);
          break;
        }
        case MULTIPLY, ADD: {
          buildNaturalCongruenceRecursively(term.subTerms(), result);
          break;
        }
        default: continue;
      }
    }
  }

  public static NaturalCongruence<UTerm> buildNaturalCongruence(List<UTerm> terms) {
//        NaturalCongruence<UTerm> result = NaturalCongruence.mk();
//        for (UTerm term : terms) {
//          if (!(term instanceof UPred)) continue;
//          UPred pred = (UPred) term;
//          if (!pred.isPredKind(EQ)) continue;
//          result.putCongruent(pred.args().get(0), pred.args().get(1));
//        }
//        return result;
    NaturalCongruence<UTerm> result = NaturalCongruence.mk();
    buildNaturalCongruenceRecursively(terms, result);
    return result;
  }


  boolean checkSubSum(
          int cur, HashSet<UVar> bigBoundVars, UTerm bigBody, ArrayList<UVar> smallBoundVars, UTerm smallBody) {

    if (cur == smallBoundVars.size()) {
      for (UTerm smallTerm : smallBody.subTerms()) {
        if (bigBody.subTerms().contains(smallTerm))
          continue;
        if (smallTerm.kind() == PRED) {
          UPred pred = (UPred) smallTerm;
          if (pred.isTruePred(globalExpr) == 1) continue;
          if (pred.isPredKind(EQ)) {
            UTerm op0 = pred.args().get(0);
            UTerm op1 = pred.args().get(1);
            NaturalCongruence<UTerm> cong = buildNaturalCongruence(bigBody.subTerms());
            if (cong.isCongruent(op0, op1)) continue;
          }
        }
        if (smallTerm.kind() == NEGATION) {
          if (smallTerm.subTerms().get(0).kind() == PRED) {
            UPred pred = (UPred) smallTerm.subTerms().get(0);
            if (isNullPred(pred)) {
              if (pred.isTruePred(globalExpr) == 0) continue;
              NaturalCongruence<UTerm> cong = buildNaturalCongruence(bigBody.subTerms());
              Set<UTerm> eqTerms = cong.eqClassOf(pred.args().get(0));
              if (any(eqTerms,
                      t -> bigBody.subTerms().contains(UNeg.mk(UPred.mk(UPred.PredKind.FUNC, UName.NAME_IS_NULL, List.of(t))))))
                continue;
            }
          }
        }
        return false;
      }
      return true;
    }

    final UVar curVar = smallBoundVars.get(cur);
    final UVar newVar = UVar.mkBase(UName.mk(Liastar.newVarName()));
    smallBody = smallBody.replaceVar(curVar, newVar, true);

    for (UVar v : bigBoundVars) {
      final HashSet<UVar> tmpVars = new HashSet<>(bigBoundVars);
      tmpVars.remove(v);
      final UTerm tmpBigBody = bigBody.replaceVar(v, newVar, true);
      final UTerm tmpSmallBody = smallBody.replaceVar(v, newVar, false);
      final boolean result = checkSubSum(cur + 1, tmpVars, tmpBigBody, smallBoundVars, tmpSmallBody);
      if (result) return true;
    }
    return false;
  }

  public boolean containSubTerms(USum bigSum, USum smallSum) {
    UTerm bigBody = bigSum.body().copy();
    UTerm smallBody = smallSum.body().copy();
    HashSet<UVar> bigBoundVars = new HashSet<>(bigSum.boundedVars());
    ArrayList<UVar> smallBoundVars = new ArrayList<>(smallSum.boundedVars());

    if (bigBoundVars.size() < smallBoundVars.size()) return false;
    if (bigSum.equals(smallSum)) return true;

    return checkSubSum(0, bigBoundVars, bigBody, smallBoundVars, smallBody);
  }

//      private static boolean mapElements(List<UVar> bigBoundedVars,
//                                      List<UVar> smallBoundedVars,
//                                      int index,
//                                      Map<UVar, UVar> mapping,
//                                      USum bigSum,
//                                      USum smallSum) {
//        if (index == smallBoundedVars.size()) {
//          int replaceNumber = 1195;
//          USum bigSumCopy = (USum) bigSum.copy();
//          USum smallSumCopy = (USum) smallSum.copy();
//          for(Map.Entry<UVar, UVar> entry: mapping.entrySet()) {
//            UVar smallVar = entry.getKey();
//            UVar bigVar = entry.getValue();
//            smallSumCopy = (USum) smallSumCopy.replaceVar(smallVar, UVar.mkBase(UName.mk("c" + replaceNumber)), true);
//            smallSumCopy = (USum) smallSumCopy.replaceVar(bigVar, UVar.mkBase(UName.mk("c" + replaceNumber)), false);
//            bigSumCopy = (USum) bigSumCopy.replaceVar(bigVar, UVar.mkBase(UName.mk("c" + replaceNumber)), true);
//            replaceNumber ++;
//          }
//          UTerm smallBody = smallSumCopy.body();
//          UTerm bigBody = bigSumCopy.body();
//          if (bigBody.kind() != MULTIPLY || smallBody.kind() != MULTIPLY)
//            return false;
//          for (UTerm smallTerm : smallBody.subTerms()) {
//            if (smallTerm.kind() == PRED) {
//              UPred pred = (UPred) smallTerm;
//              if (pred.isTruePred() == 1) continue;
//            }
//            if (smallTerm.kind() == NEGATION) {
//              if (smallTerm.subTerms().get(0).kind() == PRED){
//                UPred pred = (UPred) smallTerm.subTerms().get(0);
//                if(isNullPred(pred)) {
//                  if (pred.isTruePred() == 0) continue;
//                }
//              }
//            }
//            if (!bigBody.subTerms().contains(smallTerm))
//              return false;
//          }
//          return true;
//        } else {
//          for (int i = 0; i < bigBoundedVars.size(); i++) {
//            if (!mapping.containsValue(bigBoundedVars.get(i))) {
//              mapping.put(smallBoundedVars.get(index), bigBoundedVars.get(i));
//              if(mapElements(bigBoundedVars, smallBoundedVars, index + 1, mapping, bigSum, smallSum))
//                return true;
//              mapping.remove(smallBoundedVars.get(index));
//            }
//          }
//          return false;
//        }
//      }

  /** bigSum: sum{t1, ...}(E1(t1) * ... * E2(t1))
   *  smallSum: sum{t2, ...}(e1(t2) * ... * e2(t2))
   *  check whether each subterm in smallSum is contained by the body of bigSum
   */
//      private boolean containSubTerms(USum bigSum, USum smallSum) {
//        Set<UVar> bigBoundedVars = bigSum.boundedVars();
//        Set<UVar> smallBoundedVars = smallSum.boundedVars();
//        if(smallBoundedVars.size() != 1) {
//          if(bigBoundedVars.size() < smallBoundedVars.size())
//            return false;
//          final List<UVar> bigBoundedList = new ArrayList<>(bigBoundedVars);
//          final List<UVar> smallBoundedList = new ArrayList<>(smallBoundedVars);
//          final Map<UVar, UVar> mapping = new HashMap<>();
//          boolean result = mapElements(bigBoundedList, smallBoundedList, 0, mapping, bigSum, smallSum);
//          return result;
//        }
//        start:
//        for (UVar bigVar : bigBoundedVars) {
//          UVar smallVar = new ArrayList<>(smallBoundedVars).get(0);
//          smallSum = (USum) smallSum.replaceVar(smallVar, UVar.mkBase(UName.mk("c1195")), true);
//          smallSum = (USum) smallSum.replaceVar(bigVar, UVar.mkBase(UName.mk("c1195")), false);
//          bigSum = (USum) bigSum.replaceVar(bigVar, UVar.mkBase(UName.mk("c1195")), true);
//          UTerm smallBody = smallSum.body();
//          UTerm bigBody = bigSum.body();
//          if (bigBody.kind() != MULTIPLY || smallBody.kind() != MULTIPLY)
//            continue start;
//          for (UTerm smallTerm : smallBody.subTerms()) {
//            if (smallTerm.kind() == PRED) {
//              UPred pred = (UPred) smallTerm;
//              if (pred.isTruePred() == 1) continue;
//            }
//            if (smallTerm.kind() == NEGATION) {
//              if (smallTerm.subTerms().get(0).kind() == PRED){
//                UPred pred = (UPred) smallTerm.subTerms().get(0);
//                if(isNullPred(pred)) {
//                  if (pred.isTruePred() == 0) continue;
//                }
//              }
//            }
//            if (!bigBody.subTerms().contains(smallTerm))
//              continue start;
//          }
//          return true;
//        }
//        return false;
//      }

  // return whether the term only uses var
  private boolean termNotUseOtherVar(UVar var, UTerm term) {
    switch (term.kind()) {
      case CONST: {
        return true;
      }
      case VAR: case TABLE: {
        return term.isUsing(var);
      }
      case PRED: {
        List<UTerm> args = ((UPred) term).args();
        for (UTerm arg : args) {
          if (!termNotUseOtherVar(var, arg)) return false;
        }
        return true;
      }
      case SQUASH: {
        return termNotUseOtherVar(var, ((USquash) term).body());
      }
      case NEGATION: {
        return termNotUseOtherVar(var, ((UNeg) term).body());
      }
      default: {
        return false;
      }
    }
  }

  // return terms using only var without otherVars
  private ArrayList<UTerm> termsNotUseOtherVars(UVar var, List<UTerm> terms) {
    ArrayList<UTerm> result = new ArrayList<>();
    for (UTerm term : terms) {
      if (termNotUseOtherVar(var, term)) result.add(term);
    }
    return result;
  }

  private boolean otherTermsNotUseVar(UVar var, ArrayList<UTerm> termsUseVar, List<UTerm> allTerms) {
    for (UTerm t : allTerms) {
      if (termsUseVar.contains(t)) continue;
      if (t.isUsing(var)) return false;
    }
    return true;
  }


  /**
   * E * || sum{...}(E * e) || = E * || sum{...}(e) || or
   * E * not( sum{...}(E * e) ) = E * not( sum{...}(e) )
   */
  private UTerm removeDupSubTerm(UTerm expr) {
    expr = transformSubTerms(expr, this::removeDupSubTerm);
    UKind kind = expr.kind();
    if (kind != MULTIPLY) return expr;

    UMul mul = (UMul) expr;
    List<UTerm> subTerms = mul.subTerms();
    HashMap<UTerm, UTerm> replacedTerms = new HashMap<>();
    for (UTerm subterm : subTerms) {
      if (!(subterm instanceof USquash || subterm instanceof UNeg)) continue;
      UTerm sum = (subterm.kind() == NEGATION) ? ((UNeg) subterm).body() : ((USquash) subterm).body();
      if (!(sum instanceof USum)) continue;
      UTerm sumBody = ((USum) sum).body();
      if (!(sumBody instanceof UMul)) continue;
      for (UTerm t : subTerms) {
        if (sumBody.subTerms().contains(t)) {
          ArrayList<UTerm> newSumBody = new ArrayList<>(sumBody.subTerms());
          newSumBody.remove(t);
          USum newSum = USum.mk(((USum) sum).boundedVars(), UMul.mk(newSumBody));
          UTerm newSubTerm = (subterm instanceof USquash) ? USquash.mk(newSum) : UNeg.mk(newSum);
          replacedTerms.put(subterm, newSubTerm);
          isModified = true;
          break;
        }
      }
    }

    ArrayList<UTerm> newMulTerms = new ArrayList<>();
    for (UTerm t : subTerms) {
      if (replacedTerms.containsKey(t))
        newMulTerms.add(replacedTerms.get(t));
      else
        newMulTerms.add(t);
    }
    return UMul.mk(newMulTerms);
  }

  private List<UVarTerm> SearchEqTuple(UVarTerm tuple, List<UTerm> subTerms, boolean singleTuple) {
    ArrayList<UVarTerm> candidates = new ArrayList<>();
    for (UTerm subTerm : subTerms) {
      if (subTerm.kind() == PRED) {
        UPred pred = (UPred) subTerm;
        if (pred.isPredKind(EQ)) {
          UTerm op0 = pred.args().get(0);
          UTerm op1 = pred.args().get(1);
          if (op0.equals(tuple) && !op1.equals(tuple) && op1 instanceof UVarTerm)
            candidates.add((UVarTerm) op1);
          else if (op1.equals(tuple) && !op0.equals(tuple) && op0 instanceof UVarTerm)
            candidates.add((UVarTerm) op0);
        }
      }
    }
    if (!singleTuple) {
      return candidates;
    } else {
      switch (candidates.size()) {
        case 0:
          return candidates;
        case 1:
          return List.of(candidates.get(0));
        default: {
          for (UVarTerm v : candidates) {
            if (isOutAggVar(v)) return List.of(v);
          }
          return List.of(candidates.get(0));
        }
      }
    }
  }

  private HashMap<UVarTerm, UVarTerm> buildCongruence(UVar boundedVar, USum summation) {
    final HashMap<UVarTerm, UVarTerm> replacedTermsMap = new HashMap<>();
    if (boundedVar.is(UVar.VarKind.BASE) || boundedVar.is(UVar.VarKind.CONCAT)) {
      final List<Value> varSchema = translator.getTupleVarSchema(boundedVar);
      for (Value v : varSchema) {
        final UVarTerm targetProjVarTerm = UVarTerm.mk(translator.mkProjVar(v, boundedVar));
        final List<UVarTerm> replacedTerms =
                SearchEqTuple(targetProjVarTerm, summation.body().subTerms(), true);
        if (replacedTerms.isEmpty()) continue;
        replacedTermsMap.put(targetProjVarTerm, replacedTerms.get(0));
      }
      return replacedTermsMap;
    } else {
      final UVarTerm targetProjVarTerm = UVarTerm.mk(boundedVar);
      final List<UVarTerm> replacedTerms =
              SearchEqTuple(targetProjVarTerm, summation.body().subTerms(), true);
      if (replacedTerms.isEmpty()) return replacedTermsMap;
      replacedTermsMap.put(targetProjVarTerm, replacedTerms.get(0));
      return replacedTermsMap;
    }
  }


  private UTerm removeUselessSubSumUnderDedup(USum sum) {
    UTerm sumBody = sum.body();
    if (!(sumBody instanceof UMul))
      return sum;

    HashSet<UVar> finalVars = new HashSet<>(sum.boundedVars());
    ArrayList<UTerm> finalBody = new ArrayList<>(sum.body().subTerms());
    if (finalVars.size() <= 1) return sum;

    for (UVar boundedVar : sum.boundedVars()) {
      ArrayList<UTerm> termsUseVar = new ArrayList<>();
      all(finalBody, t -> {if(t.isUsing(boundedVar)) termsUseVar.add(t); return true;} );

      USum curSummation = USum.mk(finalVars, UMul.mk(finalBody));
      HashMap<UVarTerm, UVarTerm> congruence = buildCongruence(boundedVar, curSummation);

      for (int i = 0; i < termsUseVar.size(); ++i) {
        UTerm bodySubTerm = termsUseVar.get(i);
        if (bodySubTerm.kind() == PRED || bodySubTerm.kind() == TABLE) continue;
        for (UVarTerm varTerm : congruence.keySet()) {
          bodySubTerm =
                  bodySubTerm.replaceVar(varTerm.var(), congruence.get(varTerm).var(), false);
        }
        if (!bodySubTerm.isUsing(boundedVar))
          termsUseVar.set(i, null);
      }
      termsUseVar.removeIf(Objects::isNull);
      if (termsUseVar.size() == 0) continue;

      HashSet<UVar> boundedVars = new HashSet<>();
      boundedVars.add(boundedVar);
      USum sumOfBoundedVar = USum.mk(boundedVars, UMul.mk(termsUseVar));

      for (UVar otherVar : sum.boundedVars()) {
        if (boundedVar.equals(otherVar)) continue;
        if (!finalVars.contains(otherVar)) continue;
        HashSet<UVar> otherBoundedVars = new HashSet<>();
        otherBoundedVars.add(otherVar);
        ArrayList<UTerm> termsUseOtherVar = new ArrayList<>();
        all(finalBody, t -> {if(t.isUsing(otherVar)) termsUseOtherVar.add(t); return true;} );
        USum otherSum = USum.mk(otherBoundedVars, UMul.mk(termsUseOtherVar));
        if (containSubTerms(otherSum, sumOfBoundedVar)) {
          finalVars.remove(boundedVar);
          finalBody.removeAll(termsUseVar);
          for (int i = 0; i < finalBody.size(); ++i) {
            UTerm bodySubTerm = finalBody.get(i);
            if (bodySubTerm.kind() == PRED || bodySubTerm.kind() == TABLE) continue;
            for (UVarTerm varTerm : congruence.keySet()) {
              bodySubTerm =
                      bodySubTerm.replaceVar(varTerm.var(), congruence.get(varTerm).var(), false);
            }
            finalBody.set(i, bodySubTerm);
          }
          isModified = true;
          break;
        }
      }
    }

    if (finalVars.isEmpty())
      return (finalBody.size() == 1) ? finalBody.get(0) : UMul.mk(finalBody);
    else
      return USum.mk(finalVars, UMul.mk(finalBody));
  }

  private UTerm removeUselessMaxMinSumUnderDedup(USum sum) {
    UTerm sumBody = sum.body();
    if (!(sumBody instanceof UMul))
      return sum;

    HashMap<UVar, ArrayList<UTerm>> varToTerms = new HashMap<>();
    for (UVar var : sum.boundedVars()) {
      ArrayList<UTerm> termsUseVar = new ArrayList<>();
      all(sumBody.subTerms(), t -> {if(t.isUsing(var)) termsUseVar.add(t); return true;} );
      if (!termsUseVar.isEmpty())
        varToTerms.put(var, termsUseVar);
    }
    HashSet<UVar> finalVars = new HashSet<>(sum.boundedVars());
    ArrayList<UTerm> finalBody = new ArrayList<>(sum.body().subTerms());
    for (UVar v : varToTerms.keySet()) {
      ArrayList<UTerm> termsUseVar = varToTerms.get(v);
      if (termsUseVar.size() != 3) continue;
      List<UTerm> compareSourceSumSubTerms = new ArrayList<>();
      USum compareTargetSum = null;
      for (UTerm termUse : termsUseVar) {
        if (termUse.kind() == NEGATION && ((UNeg) termUse).body().kind() == SUMMATION) {
          compareTargetSum = (USum) ((UNeg) termUse).body();
        } else compareSourceSumSubTerms.add(termUse);
      }
      if (compareTargetSum == null) break;
      USum compareSourceSum = USum.mk(Set.of(v), UMul.mk(compareSourceSumSubTerms));
      if (containSubTerms(compareTargetSum, compareSourceSum)) {
        if (compareTargetSum.boundedVars().size() != 1 || compareSourceSum.boundedVars().size() != 1)
          break;
        final UVar targetBoundedVar = compareTargetSum.boundedVars().iterator().next();
        final UVar sourceBoundedVar = compareSourceSum.boundedVars().iterator().next();
        for (UTerm targetSubTerm : compareTargetSum.body().subTerms()) {
          if (targetSubTerm.kind() == PRED) {
            UPred pred = (UPred) targetSubTerm;
            if (pred.isPredKind(UPred.PredKind.GT) || pred.isPredKind(UPred.PredKind.LT)) {
              assert pred.args().size() == 2;
              if ((pred.args().get(0).isUsing(sourceBoundedVar) && pred.args().get(1).isUsing(targetBoundedVar)) ||
                      (pred.args().get(1).isUsing(sourceBoundedVar) && pred.args().get(0).isUsing(targetBoundedVar))) {
                finalVars.remove(v);
                finalBody.removeAll(termsUseVar);
                isModified = true;
              }
            }
          }
        }
      }
    }

    if (finalVars.isEmpty())
      return (finalBody.size() == 1) ? finalBody.get(0) : UMul.mk(finalBody);
    else
      return USum.mk(finalVars, UMul.mk(finalBody));
  }

  private UTerm removeUselessMaxMinNegUnderDedup(USum sum) {
    UTerm sumBody = sum.body();
    if (!(sumBody instanceof UMul))
      return sum;

    HashSet<UVar> finalVars = new HashSet<>(sum.boundedVars());
    ArrayList<UTerm> finalBody = new ArrayList<>(sum.body().subTerms());

    HashMap<UVar, List<UTerm>> varToTerms = new HashMap<>();
    for (UVar var : sum.boundedVars()) {
      List<UTerm> termsUseVar = new ArrayList<>();
      all(sumBody.subTerms(), t -> {if(t.isUsing(var)) termsUseVar.add(t); return true;} );
      if (!termsUseVar.isEmpty())
        varToTerms.put(var, termsUseVar);
    }

    for (UVar v : varToTerms.keySet()) {
      List<UTerm> subTerms = varToTerms.get(v);
      List<UTerm> compareTerms = new ArrayList<>();
      UNeg negation = null;
      boolean hasMax = false;
      boolean hasMin = false;

      for (UTerm subTerm : subTerms) {
        if (subTerm instanceof UNeg neg) {
          if (neg.body() instanceof USum)
            negation = neg;
          else break;
          continue;
        }
        if (subTerm instanceof UPred pred && pred.isBinaryPred()) {
          assert pred.args().size() == 2;
          UTerm firstArg = pred.args().get(0);
          UTerm secondArg = pred.args().get(1);
          if ((firstArg.isUsing(v) && !secondArg.isUsing(v)) ||
                  (!firstArg.isUsing(v) && secondArg.isUsing(v))) {
            if (pred.isPredKind(UPred.PredKind.GT)) {
              hasMax = true;
              continue;
            }
            if (pred.isPredKind(UPred.PredKind.LT)) {
              hasMin = true;
              continue;
            }
          }
        }
        compareTerms.add(subTerm);
      }

      if (negation == null)
        continue;

      USum compareTargetSum = (USum) negation.body();
      USum compareSourceSum = USum.mk(Set.of(v), UMul.mk(compareTerms));

      if (containSubTerms(compareTargetSum, compareSourceSum)) {
        for (UTerm targetSubTerm : compareTargetSum.body().subTerms()) {
          if (targetSubTerm instanceof UPred pred && pred.isBinaryPred()) {
            assert pred.args().size() == 2;
            UTerm secondArg = pred.args().get(1);
            if (((pred.isPredKind(UPred.PredKind.GT)) && hasMax && secondArg.isUsing(v)) ||
                    ((pred.isPredKind(UPred.PredKind.LT)) && hasMin && secondArg.isUsing(v))) {
              finalBody.remove(negation);
              isModified = true;
            } else if (((pred.isPredKind(UPred.PredKind.GT)) && (!hasMax && !hasMin) && secondArg.isUsing(v)) ||
                    ((pred.isPredKind(UPred.PredKind.LT)) && (!hasMax && !hasMin) && secondArg.isUsing(v))) {
              finalBody.remove(negation);
              isModified = true;
            }
          }
        }
      }
    }

    if (finalVars.isEmpty())
      return (finalBody.size() == 1) ? finalBody.get(0) : UMul.mk(finalBody);
    else
      return USum.mk(finalVars, UMul.mk(finalBody));
  }

  /**
   *   not( sum{t1, t2}([ISNULL(t1)] * ...) * ...)
   * = not( (sum{t2}(0 * ...) + sum{t2}(1 * ...))* ... )
   * when the [ISNULL(t1)] is only the term which contains t1
   */
  private UTerm replaceUselessNegSumWithNumber(UTerm term) {
    term = transformSubTerms(term, this::replaceUselessNegSumWithNumber);
    UKind kind = term.kind();
    if (kind != NEGATION) return term;

    UTerm body = ((UNeg) term).body();
    UTerm newBody = null;
    switch (body.kind()) {
      case SUMMATION: {
        newBody = replaceUselessSumWithNumberUnderNeg((USum) body);
        break;
      }
      case MULTIPLY: {
        ArrayList<UTerm> newSubTerms = new ArrayList<>();
        for (UTerm subTerm : body.subTerms()) {
          if (subTerm.kind() == SUMMATION)
            newSubTerms.add(replaceUselessSumWithNumberUnderNeg((USum) subTerm));
          else
            newSubTerms.add(subTerm);
        }
        newBody = UMul.mk(newSubTerms);
        break;
      }
      default: newBody = body;
    }

    return UNeg.mk(newBody);
  }

  private UTerm findVarIsNullPred(UTerm term, UVar var) {
    if (term instanceof UPred pred && pred.isPredKind(UPred.PredKind.FUNC)) {
      if (pred.predName().equals(UName.NAME_IS_NULL) && pred.isUsing(var)) {
        return pred;
      }
    }

    for (final UTerm subTerm : term.subTerms()) {
      UTerm tgtTerm = null;
      if ((tgtTerm = findVarIsNullPred(subTerm, var)) != null)
        return tgtTerm;
    }

    return null;
  }

  private UTerm replaceUselessSumWithNumberUnderNeg(USum sum) {
    if (sum.body().kind() != MULTIPLY) return sum;
    Set<UVar> boundedVars = sum.boundedVars();

    List<UTerm> subTerms = sum.body().subTerms();
    HashMap<UVar, UTerm> replaceMap = new HashMap<>();

    for (UVar boundedVar : boundedVars) {
      for (UTerm subTerm : subTerms) {
        UTerm tgtTerm = findVarIsNullPred(subTerm, boundedVar);
        if (tgtTerm != null) {
          replaceMap.put(boundedVar, tgtTerm);
          break;
        }
      }
    }

    for (Map.Entry<UVar, UTerm> entry : replaceMap.entrySet()) {
      UVar boundedVar = entry.getKey();
      UTerm tgtTerm = entry.getValue();
      UTerm newSumZero = sum.copy().replaceAtomicTerm(tgtTerm, UConst.zero());
      UTerm newSumOne = sum.copy().replaceAtomicTerm(tgtTerm, UConst.one());
      // only isnull contains boundedVar, else continue
      if (newSumZero instanceof USum sumZero) {
        if (sumZero.boundedVars().contains(boundedVar))
          continue;
      }
      isModified = true;
      return UAdd.mk(newSumZero, newSumOne);
    }
    return sum;
  }

  /** for a sum, if it contains a targetTerm(which has baseVar), delete the correlated boundedVar
   *  sum: \sum{t, x, y}(E(t) * ...), targetTerm: E(u), baseVar: u
   *  sum -> \sum{x, y}(...)
   * */
  private UTerm removeUselessSumUnderConflict(USum sum, UTerm targetTerm, UVar baseVar) {
    boolean deleted = true;
    while (deleted) {
      deleted = false;
      UVar toDeleteVar = null;
      List<UTerm> toDeleteTerms = new ArrayList<>();
      for (final UVar boundedVar : sum.boundedVars()) {
        final UTerm cmpTerm = targetTerm.copy().replaceVar(baseVar, boundedVar, true);
        final UTerm srcTerm = UMul.mk(filter(sum.body().subTerms(), t -> t.isUsing(boundedVar)));
        if (srcTerm.equals(cmpTerm)) {
          deleted = true;
          toDeleteVar = boundedVar;
          toDeleteTerms = filter(sum.body().subTerms(), t -> t.isUsing(boundedVar));
          break;
        }
      }
      if (deleted) {
        isModified = true;
        sum.body().subTerms().removeAll(toDeleteTerms);
        sum.removeBoundedVar(toDeleteVar);
      }
    }
    if (sum.boundedVars().size() == 0 && sum.body().subTerms().size() == 0) return UConst.one();
    return sum;
  }

  private UTerm removeUselessSumUnderDedup(USum sum) {
    UTerm term = removeUselessSubSumUnderDedup(sum);
    if (term instanceof USum)
      term = removeUselessMaxMinSumUnderDedup((USum) term);
    if (term instanceof USum)
      term = removeUselessMaxMinNegUnderDedup((USum) term);
    if (term instanceof USum)
      term = removeUselessDistinctAggBoundedVar((USum) term);
    if (term instanceof USum)
      term = removeAggNegCond((USum) term);
    return term;
  }

  private UTerm removeUselessSquashNegDupSum(UTerm term) {
    term = transformSubTerms(term, this::removeUselessSquashNegDupSum);
    UKind kind = term.kind();
    if (kind != NEGATION && kind != SQUASH) return term;

    UTerm body = (kind == NEGATION) ? ((UNeg) term).body() : ((USquash) term).body();
    UTerm newBody = null;
    switch (body.kind()) {
      case SUMMATION: {
        newBody = removeUselessSumUnderDedup((USum) body);
        break;
      }
      case ADD: {
        ArrayList<UTerm> newSubTerms = new ArrayList<>();
        for (UTerm subTerm : body.subTerms()) {
          if (subTerm.kind() == SUMMATION)
            newSubTerms.add(removeUselessSumUnderDedup((USum) subTerm));
          else
            newSubTerms.add(subTerm);
        }
        newBody = UAdd.mk(newSubTerms);
        break;
      }
      default: newBody = body;
    }

    return (kind == NEGATION) ? UNeg.mk(newBody) : USquash.mk(newBody);
  }

  /**
   *   sum{t1, ...}(||sum{t2, ...}E1(t2)|| * E1(t1) * E2(t1))
   * = sum{t1, ...}(E1(t1) * E2(t1))
   */
  private UTerm removeUselessSquashSumFromSumBody(UTerm term) {
    term = transformSubTerms(term, this::removeUselessSquashSumFromSumBody);
    if (term.kind() != SUMMATION) return term;

    USum expr = (USum) term;
    UTerm body = expr.body();
    if (!(body instanceof UMul))
      return expr;
    for (UTerm subTerm : body.subTerms()) {
      if (subTerm instanceof USquash) {
        UTerm squashBody = ((USquash) subTerm).body();
        if (squashBody instanceof USum) {
          USum squashSum = (USum) squashBody;
          if (squashSum.boundedVars().size() > expr.boundedVars().size())
            continue;
          ArrayList<UTerm> subTerms = new ArrayList<>();
          subTerms.addAll(body.subTerms());
          subTerms.remove(subTerm);
          USum tmp = USum.mk(expr.boundedVars(), UMul.mk(subTerms));
          if (containSubTerms(tmp, squashSum)) {
            isModified = true;
            return tmp;
          }
        }
      }
    }
    return expr;
  }

  /**
   *   sum{t1, ...}(not(sum{t2, ...}E1(t2)) * E1(t1) * E2(t1))
   *   = 0
   */
  private UTerm removeUselessSumWithNegation(UTerm term) {
    term = transformSubTerms(term, this::removeUselessSumWithNegation);
    if (term.kind() != SUMMATION) return term;

    USum expr = (USum) term;
    UTerm body = expr.body();
    if (!(body instanceof UMul))
      return expr;
    for (UTerm subTerm : body.subTerms()) {
      if (subTerm instanceof UNeg) {
        final UTerm negBody = ((UNeg) subTerm).body();
        if (negBody instanceof USum) {
          final USum negSum = (USum) negBody;
          final ArrayList<UTerm> subTerms = new ArrayList<>();
          subTerms.addAll(body.subTerms());
          subTerms.remove(subTerm);
          final USum tmp = USum.mk(expr.boundedVars(), UMul.mk(subTerms));
          if (containSubTerms(tmp, negSum)) {
            isModified = true;
            return UConst.zero();
          }
        }
      } else if (subTerm instanceof UPred) {
        final UPred pred = (UPred) subTerm;
        if (pred.isPredKind(EQ)) {
          assert pred.args().size() == 2;
          final UTerm firstArg = pred.args().get(0);
          final UTerm secondArg = pred.args().get(1);
          UTerm focusArg = null;
          if (firstArg.equals(UConst.zero())) {
            focusArg = secondArg;
          } else if (secondArg.equals(UConst.zero())) {
            focusArg = firstArg;
          } else continue;
          if (focusArg instanceof USum) {
            final USum focusSum = (USum) focusArg;
            final ArrayList<UTerm> subTerms = new ArrayList<>();
            subTerms.addAll(body.subTerms());
            subTerms.remove(subTerm);
            final USum tmp = USum.mk(expr.boundedVars(), UMul.mk(subTerms));
            if (containSubTerms(tmp, focusSum)) {
              isModified = true;
              return UConst.zero();
            }
          }
        }
      }
    }
    return expr;
  }

  /**
   *   not( sum{t1}(E1(t1)) * ...) * E1(y)
   * = not( ... )* E1(y)
   * delete t1 and E1(t1)
   * only consider summation with one boundedVar
   * this function focus on icFreshVars, which include y
   */
  private UTerm removeUselessNegSumWithSameFilter(UTerm term) {
    term = transformSubTerms(term, this::removeUselessNegSumWithSameFilter);
    if (term.kind() != MULTIPLY) return term;
    if (icFreshVars.size() == 0) return term;


    for (final UVar icFreshVar : icFreshVars) {
      List<UTerm> targetTermList = filter(term.subTerms(), t -> t.isUsing(icFreshVar));
      List<UTerm> negList = filter(term.subTerms(), t -> !t.isUsing(icFreshVar) && t.kind() == NEGATION);
      List<UTerm> newNegList = new ArrayList<>();
      UTerm targetTerm = UMul.mk(targetTermList).copy();
      for (UTerm negTerm : negList) {
        UTerm body = ((UNeg) negTerm).body();
        UTerm newBody = null;
        switch (body.kind()) {
          case SUMMATION: {
            if (((USum) body).boundedVars().size() == 1) {
              newBody = removeUselessSumUnderConflict((USum) body, targetTerm, icFreshVar);
            } else {
              newBody = body;
            }
            break;
          }
          case MULTIPLY: {
            ArrayList<UTerm> newSubTerms = new ArrayList<>();
            for (UTerm subTerm : body.subTerms()) {
              if (subTerm.kind() == SUMMATION && ((USum) subTerm).boundedVars().size() == 1)
                newSubTerms.add(removeUselessSumUnderConflict((USum) subTerm, targetTerm, icFreshVar));
              else
                newSubTerms.add(subTerm);
            }
            newBody = UMul.mk(newSubTerms);
            break;
          }
          default: newBody = body;
        }
        newNegList.add(UNeg.mk(newBody));
      }
      term.subTerms().removeAll(negList);
      term.subTerms().addAll(newNegList);
    }

    return term;
  }

  private boolean maxminTuple(UVarTerm var) {
    String varStr = var.toString();
    return (varStr.indexOf("max") >= 0) || (varStr.indexOf("min") >= 0);
  }


  /**
   * Search for
   * not(∑{x8}(emp(x8) * [emp.sal(x10) = emp.sal(x8)] * [emp.comm(x8) < t2.min1(x10)])) or
   * not(∑{x8}(emp(x8) * [emp.sal(x10) = emp.sal(x8)] * [emp.comm(x8) > t2.min1(x10)]))
   */
  private UTerm maxminNegPred(UVarTerm maxminVar, UTerm term, UTerm[] maxminTerms) {
    if (term.kind() != NEGATION) return null;

    UTerm negBody = ((UNeg) term).body();
    if (negBody.kind() != SUMMATION) return null;
    USum sum = (USum) negBody;
    ArrayList<UVar> sumVars = new ArrayList<>(sum.boundedVars());
    if (sumVars.size() != 1) return null;
    if (sum.body().kind() != MULTIPLY) return null;
    UMul sumBody = (UMul) sum.body();
    ArrayList<UTerm> sumSubTerms = new ArrayList<>(sumBody.subTerms());
    for (UTerm subterm : sumSubTerms) {
      if (subterm.kind() != PRED) continue;
      UPred pred = (UPred) subterm;
      if (pred.predKind() != UPred.PredKind.LT && pred.predKind() != UPred.PredKind.GT) continue;
      List<UTerm> args = pred.args();
      assert args.size() == 2;
      if (args.get(1).equals(maxminVar)) {
        maxminTerms[1] = term;
        ArrayList<UTerm> newSubTerms = new ArrayList<>(sumSubTerms);
        newSubTerms.remove(pred);
        UTerm groupByCond = USquash.mk(USum.mk(sum.boundedVars(), UMul.mk(newSubTerms)));
        return groupByCond;
      }
    }
    return null;
  }

  /**
   * Search for
   * ||∑{x9, ...}(emp(x9) * [emp.sal(x10) = emp.sal(x9)] * [emp.comm(x9) = t2.min1(x10)] * E)||
   */
  private UTerm maxminSquashPred(UVarTerm maxminVar, UTerm term, UTerm[] maxminTerms) {
    if (term.kind() != SQUASH) return null;

    UTerm squashBody = ((USquash) term).body();
    if (squashBody.kind() != SUMMATION) return null;
    USum sum = (USum) squashBody;
    ArrayList<UVar> sumVars = new ArrayList<>(sum.boundedVars());
    if (sum.body().kind() != MULTIPLY) return null;
    UMul sumBody = (UMul) sum.body();
    ArrayList<UTerm> sumSubTerms = new ArrayList<>(sumBody.subTerms());
    for (UVar boundedVar : sumVars) {
      List<UTerm> termsUsingVar = sumSubTerms.stream()
              .filter(t -> t.isUsing(boundedVar))
              .collect(Collectors.toList());
      for (UTerm subterm : termsUsingVar) {
        if (any(sumVars, v -> !v.equals(boundedVar) && subterm.isUsing(v))) return null;
        if (subterm.kind() != PRED) continue;
        UPred pred = (UPred) subterm;
        if (pred.predKind() != EQ) continue;
        List<UTerm> args = pred.args();
        assert args.size() == 2;
        if (args.get(1).equals(maxminVar)) {
          ArrayList<UTerm> newSubTerms = new ArrayList<>(termsUsingVar);
          newSubTerms.remove(pred);
          HashSet<UVar> newBoundedVars = new HashSet<>();
          newBoundedVars.add(boundedVar);
          UTerm groupByCond = USquash.mk(USum.mk(newBoundedVars, UMul.mk(newSubTerms)));

          maxminTerms[2] = term;
          if (sumVars.size() == 1) {
            maxminTerms[3] = null;
          } else {
            HashSet<UVar> otherBoundedVars = new HashSet<>(sumVars);
            otherBoundedVars.remove(boundedVar);
            ArrayList<UTerm> otherTerms = new ArrayList<>(sumSubTerms);
            otherTerms.removeAll(termsUsingVar);
            maxminTerms[3] = USquash.mk(USum.mk(otherBoundedVars, UMul.mk(otherTerms)));
          }
          return groupByCond;
        }
      }
    }
    return null;
  }


  /**
   * search for E(t) * not(\sum{t1}(E(t1) * [a(t1) < maxminVal]))
   * or E(t) * not(\sum{t1}(E(t1) * [a(t1) > maxminVal]))
   * maxminVal is an attribute of t
   */
  private boolean isMaxMinValue(UVar var, UVarTerm maxminVal, List<UTerm> subTerms, UTerm[] maxminTerms) {
    UTerm[] maxminPreds = new UTerm[4];
    UTerm groupByCond = null;
    for (UTerm term : subTerms) {
      groupByCond = maxminNegPred(maxminVal, term, maxminPreds);
      if (groupByCond != null)
        break;
    }
    if (groupByCond == null)
      return false;

    ArrayList<UTerm> groupByConds = new ArrayList<>(((USquash) groupByCond).body().subTerms());
    if (all(groupByConds, t -> subTerms.contains(t))) {
      maxminTerms[0] = groupByCond;
      maxminTerms[1] = maxminPreds[1];
      return true;
    } else {
      return false;
    }
  }


  /**
   * Search for
   * not(∑{x8}(emp(x8) * [emp.sal(x10) = emp.sal(x8)] * [emp.comm(x8) < t2.min1(x10)])) *
   * ||∑{x9}(emp(x9) * [emp.sal(x10) = emp.sal(x9)] * [emp.comm(x9) = t2.min1(x10)])||
   */
  private void searchMaxMinPred(UVarTerm maxminVar, List<UTerm> subTerms, UTerm[] maxminTerms) {
    UTerm groupByCond1 = null;
    UTerm groupByCond2 = null;
    for (UTerm term : subTerms) {
      if (groupByCond1 == null)
        groupByCond1 = maxminNegPred(maxminVar, term, maxminTerms);
      if (groupByCond2 == null)
        groupByCond2 = maxminSquashPred(maxminVar, term, maxminTerms);
    }
    if (groupByCond1 == null || groupByCond2 == null)
      return;
    if (groupByCond1.equals(groupByCond2)) {
      maxminTerms[0] = groupByCond1;
    }
  }

  private ArrayList<UVarTerm> selectEqTuples(UVarTerm var, List<UTerm> subTerms) {
    ArrayList<UVarTerm> result = new ArrayList<>();
    for (UTerm t : subTerms) {
      if (t.kind() == PRED) {
        UPred pred = (UPred) t;
        if (pred.isPredKind(EQ) && pred.args().contains(var)) {
          UTerm otherTuple = (pred.args().get(0).equals(var)) ? pred.args().get(1) : pred.args().get(0);
          if (otherTuple instanceof UVarTerm)
            result.add((UVarTerm) otherTuple);
        }
      }
    }
    return result;
  }


  /**
   * ∑{x19}(not(∑{x18}(E(x18) * [emp.comm(x18) < %1(x)])) * E(x19) * [emp.comm(x19) = %1(x)])
   * =>
   * not(∑{x18}(E(x18) * [emp.comm(x18) < %1(x)])) * ∑{x19}(E(x19) * [emp.comm(x19) = %1(x)])
   */
  private UTerm removeAggNegCond(USum expr) {
    final Set<UVar> boundedVars = new HashSet<>(expr.boundedVars());
    final List<UTerm> subTerms = expr.body().subTerms();
    if (!(expr.body() instanceof UMul) || (subTerms.size() == 1))
      return expr;

    ArrayList<UTerm> removedSubTerm = new ArrayList<>();
    for (UVar boundedVar : boundedVars) {
      List<Value> varSchema = translator.getTupleVarSchema(boundedVar);
      for (Value v : varSchema) {
        final UVarTerm targetProjVarTerm = UVarTerm.mk(translator.mkProjVar(v, boundedVar));
        List<UVarTerm> eqTuples = SearchEqTuple(targetProjVarTerm, expr.body().subTerms(), false);
        for (UVarTerm eqTuple : eqTuples) {
          if (eqTuple == null || !isOutAggVar(eqTuple)) continue;
          UTerm groupByCond = null;
          for (UTerm subterm : subTerms) {
            groupByCond = maxminNegPred(eqTuple, subterm, new UTerm[4]);
            if (groupByCond != null) {
              USum groupByBody = (USum) ((USquash) groupByCond).body();
              if (containSubTerms(expr, groupByBody)) {
                removedSubTerm.add(subterm);
              }
            }
          }
        }
      }
    }

    ArrayList<UTerm> newSubTerms = new ArrayList<>(subTerms);
    for (int i = 0; i < newSubTerms.size(); ++i) {
      UTerm term = newSubTerms.get(i);
      if (removedSubTerm.contains(term)) {
        UNeg negation = (UNeg) term;
        USum tmpSum = (USum) negation.body();
        HashSet<UVar> allowedVars = new HashSet<>(tmpSum.boundedVars());
        allowedVars.add(tail(translator.visibleVars));
        ArrayList<UTerm> newTmpSumSubTerms = new ArrayList<>();
        for (UTerm t : tmpSum.body().subTerms()) {
          if (t.kind() == PRED && ((UPred) t).isPredKind(EQ)) {
            UTerm op0 = ((UPred) t).args().get(0);
            UTerm op1 = ((UPred) t).args().get(1);
            if (all(allowedVars, v -> !op0.isUsing(v)) || all(allowedVars, v -> !op1.isUsing(v))) {
              isModified = true;
              continue;
            }
          }
          newTmpSumSubTerms.add(t);
        }
        newSubTerms.set(i, UNeg.mk(USum.mk(tmpSum.boundedVars(), UMul.mk(newTmpSumSubTerms))));
      }
    }

    return USum.mk(boundedVars, UMul.mk(newSubTerms));
  }


  /**
   *
   * || sum{t, ...}(groupbyCond(t) * not(sum{t1}(groupbyCond(t1)*[a(t1) < a(t)])) * [a(t) < e]) ||
   * =>
   * || sum{t, ...}(groupbyCond(t) * [a(t) < e]) ||
   *
   * not( sum{t, ...}(groupbyCond(t) * not(sum{t1}(groupbyCond(t1)*[a(t1) < a(t)])) * [a(t) < e]) )
   * =>
   * not( sum{t, ...}(groupbyCond(t) * [a(t) < e]) )
   */
  private UTerm removeUselessDistinctAggBoundedVar(USum expr) {
    final Set<UVar> boundedVars = new HashSet<>(expr.boundedVars());
    final List<UTerm> subTerms = expr.body().subTerms();
    if (!(expr.body() instanceof UMul) || (subTerms.size() == 1))
      return expr;

    ArrayList<UTerm> removedSubTerm = new ArrayList<>();
    for (UVar boundedVar : boundedVars) {
      List<Value> varSchema = translator.getTupleVarSchema(boundedVar);
      start:
      for (Value v : varSchema) {
        final UVarTerm targetProjVarTerm = UVarTerm.mk(translator.mkProjVar(v, boundedVar));
        ArrayList<UVarTerm> eqTuples = new ArrayList<>();
        eqTuples.add(targetProjVarTerm);
        UTerm groupByCond = null;
        for (UTerm subterm : subTerms) {
          for (UVarTerm eqTuple : eqTuples) {
            groupByCond = maxminNegPred(eqTuple, subterm, new UTerm[4]);
            if (groupByCond != null) {
              USum groupByBody = (USum) ((USquash) groupByCond).body();
              if (containSubTerms(expr, groupByBody)) {
                removedSubTerm.add(subterm);
                isModified = true;
                continue start;
              }
            }
          }
        }
      }
    }

    ArrayList<UTerm> newSubTerms = new ArrayList<>(subTerms);
    newSubTerms.removeAll(removedSubTerm);

    return USum.mk(boundedVars, UMul.mk(newSubTerms));
  }

  /**
   *   ∑{x}([a(x) = e1] * [b(x) = e2] * ... * minmax(c(x)) * E)
   * = E * [minmax != 0] ( a(x) -> e1, b(x) -> e2, c(x) does not exist in E, c can be min or max )
   */
  private UTerm removeUselessAggBoundedVar(UTerm expr) {
    expr = transformSubTerms(expr, this::removeUselessAggBoundedVar);
    if (expr.kind() != SUMMATION) return expr;

    USum summation = (USum) expr;
    final Set<UVar> boundedVars = new HashSet<>(summation.boundedVars());
    final List<UTerm> subTerms = summation.body().subTerms();
    if (!(summation.body() instanceof UMul) || (subTerms.size() == 1))
      return expr;

    for (UVar boundedVar : boundedVars) {
      if (useTableVar(summation.body(), boundedVar))
        continue;
      final Map<UTerm, UTerm> replacedTermsMap = new HashMap<>();
      List<Value> varSchema = translator.getTupleVarSchema(boundedVar);
      ArrayList<Value> cannotReplaceSchema = new ArrayList<>();
      boolean hasMaxMin = false;
      for (Value v : varSchema) {
        final UVarTerm targetProjVarTerm = UVarTerm.mk(translator.mkProjVar(v, boundedVar));
        final UTerm replacedTerm;
        if ((replacedTerm = searchVarTermReplacement(targetProjVarTerm, summation)) != null) {
          replacedTermsMap.put(targetProjVarTerm, replacedTerm);
        } else if (!hasMaxMin) {
          UTerm[] maxminTerms = new UTerm[4];
          maxminTerms[0] = null;
          maxminTerms[1] = null;
          maxminTerms[2] = null;
          maxminTerms[3] = null;
          searchMaxMinPred(targetProjVarTerm, subTerms, maxminTerms);
          hasMaxMin = hasMaxMin || (maxminTerms[0] != null);
          if (maxminTerms[0] != null && maxminTerms[3] == null)
            replacedTermsMap.put(targetProjVarTerm, UMul.mk(maxminTerms[0], maxminTerms[1], maxminTerms[2]));
          else if (maxminTerms[0] != null)
            replacedTermsMap.put(targetProjVarTerm, UMul.mk(maxminTerms[0], maxminTerms[1], maxminTerms[2], maxminTerms[3]));
          else
            cannotReplaceSchema.add(v);
        } else {
          cannotReplaceSchema.add(v);
        }
      }
      if (replacedTermsMap.isEmpty())
        continue;
      isModified = true;
      for (var pair : replacedTermsMap.entrySet()) {
        final UTerm val = pair.getValue();
        if (val instanceof UPred) {
          final UPred targetPred = (UPred) val;
          if (targetPred.isPredKind(EQ)) {
            assert targetPred.args().size() == 2;
            final UTerm targetProjVarTerm = pair.getKey();
            final UTerm predArg0 = targetPred.args().get(0), predArg1 = targetPred.args().get(1);
            final UTerm replaceTerm = targetProjVarTerm.equals(predArg0) ? predArg1 : predArg0;
            summation = (USum) summation.replaceAtomicTerm(targetPred, UConst.one());
            if (replaceTerm.kind() == SUMMATION)
              summation = (USum) replaceAtomicTermWithSummation(summation, targetProjVarTerm, replaceTerm);
            else
              summation = (USum) summation.replaceAtomicTerm(targetProjVarTerm, replaceTerm);
            updateReplacedTermsMap(replacedTermsMap, targetProjVarTerm, replaceTerm);
          }
        } else {
          UTerm groupByCond = val.subTerms().get(0);
          UTerm removedNegTerm = val.subTerms().get(1);
          UTerm removedSquashTerm = val.subTerms().get(2);
          summation = (USum) summation.replaceTerm(removedNegTerm, UConst.one());
          summation = (USum) summation.replaceTerm(removedSquashTerm, UConst.one());
          summation = (USum) summation.addMulSubTerm(groupByCond);
          if (val.subTerms().size() == 4)
            summation = (USum) summation.addMulSubTerm(val.subTerms().get(3));
        }
      }
      if (cannotReplaceSchema.size() == 0)
        summation.removeBoundedVar(boundedVar);
      else
        translator.putTupleVarSchema(boundedVar, cannotReplaceSchema);
    }

    if (summation.boundedVars().isEmpty()) return summation.body();
    return summation;
  }

  private static USquash findSquashSum(List<UTerm> subTerms) {
    for (UTerm t : subTerms) {
      if (t instanceof USquash) {
        if (((USquash) t).body() instanceof USum) {
          return (USquash) t;
        }
      }
    }
    return null;
  }

  private USum removeUselessBoundedVarNestedly(Map<UTerm, UTerm> replacedTermsMap, USum expr) {
    // Replace each projVar with corresponding substitutions
    for (var pair : replacedTermsMap.entrySet()) {
      final UPred targetPred = (UPred) pair.getValue();
      if (isNullPred(targetPred)) {
        expr = (USum) propagateNullValue(expr, pair.getKey());
        expr = (USum) expr.replaceAtomicTerm(targetPred, UConst.one());
      } else if (targetPred.isPredKind(EQ)) {
        assert targetPred.args().size() == 2;
        final UTerm targetProjVarTerm = pair.getKey();
        final UTerm predArg0 = targetPred.args().get(0), predArg1 = targetPred.args().get(1);
        final UTerm replaceTerm = targetProjVarTerm.equals(predArg0) ? predArg1 : predArg0;
        expr = (USum) expr.replaceAtomicTerm(targetPred, UConst.one());
        if (replaceTerm.kind() == SUMMATION) {
          expr = (USum) replaceAtomicTermWithSummation(expr, targetProjVarTerm, replaceTerm);
        } else {
          expr = (USum) expr.replaceAtomicTerm(targetProjVarTerm, replaceTerm);
        }
        updateReplacedTermsMap(replacedTermsMap, targetProjVarTerm, replaceTerm);
      }
    }
    return expr;
  }

  private void uniqueValueForAttrs(
          UVar boundedVar,
          Map<UTerm, UTerm> replacedTermsMap,
          ArrayList<Value> cannotReplaceSchema,
          USquash squash) {
    USum squashSum = (USum) squash.body();
    final List<Value> varSchema = translator.getTupleVarSchema(boundedVar);
    for (Value v : varSchema) {
      final UVarTerm targetProjVarTerm = UVarTerm.mk(translator.mkProjVar(v, boundedVar));
      final UTerm replacedTerm;
      if ((replacedTerm = searchVarTermReplacement(targetProjVarTerm, squashSum)) != null) {
        if (replacedTerm instanceof UPred && ((UPred) replacedTerm).isPredKind(EQ)) {
          UTerm arg0 = ((UPred) replacedTerm).args().get(0);
          UTerm arg1 = ((UPred) replacedTerm).args().get(1);
          UTerm otherTuple = arg0.equals(targetProjVarTerm) ? arg1 : arg0;
          UKind otherTupleKind = otherTuple.kind();
          if (otherTupleKind != CONST && otherTupleKind != STRING) {
            cannotReplaceSchema.add(v);
            continue;
          }
        }
        replacedTermsMap.put(targetProjVarTerm, replacedTerm);
      } else {
        cannotReplaceSchema.add(v);
      }
    }
  }

  /**
   * \sum{t}(||sum{t1}[t = e]*E|| * f(t)) => ||sum{t1}E|| * f(e)
   */
  private UTerm removeUselessBoundedVarsNestedly(UTerm expr) {
    expr = transformSubTerms(expr, this::removeUselessBoundedVarsNestedly);
    if (expr.kind() != SUMMATION) return expr;

    USum summation = (USum) expr;
    final Set<UVar> boundedVars = new HashSet<>(summation.boundedVars());
    final List<UTerm> subTerms = summation.body().subTerms();
    if (!(summation.body() instanceof UMul))
      return expr;

    USquash squash = findSquashSum(subTerms);
    if (squash == null) return expr;
    USum squashSum = (USum) squash.body();
    if (squashSum.body().kind() != MULTIPLY) return expr;

    UMul squashSumBody = (UMul) squashSum.body();
    List<UTerm> innerSubTerms = squashSumBody.subTerms();
    ArrayList<UTerm> outerSubTerms = new ArrayList<>(subTerms);
    outerSubTerms.remove(squash);
    for (UVar boundedVar : boundedVars) {
      if (any(innerSubTerms, t -> useTableVar(t, boundedVar))) continue;
      if (any(outerSubTerms, t -> useTableVar(t, boundedVar))) continue;
      final Map<UTerm, UTerm> replacedTermsMap = new HashMap<>();
      final ArrayList<Value> cannotReplaceSchema = new ArrayList<>();
      uniqueValueForAttrs(boundedVar, replacedTermsMap, cannotReplaceSchema, squash);
      if (replacedTermsMap.isEmpty()) continue;
      summation = removeUselessBoundedVarNestedly(replacedTermsMap, summation);
      if (cannotReplaceSchema.isEmpty())
        summation.removeBoundedVar(boundedVar);
      else
        translator.putTupleVarSchema(boundedVar, cannotReplaceSchema);
      isModified = true;
    }

    if (summation.boundedVars().isEmpty())
      return summation.body();
    return summation;
  }

  /**
   * sum{t1}(IsNull(a(t1)) * E * [a(t1) = b(t2)]) =>
   * sum{t1}(IsNull(a(t1)) * E * IsNull(a(t2)))
   */
  private UTerm propagateNullBoundedVar(UTerm expr) {
    expr = transformSubTerms(expr, this::propagateNullBoundedVar);
    if (expr.kind() != SUMMATION) return expr;

    USum summation = (USum) expr;
    final Set<UVar> boundedVars = new HashSet<>(summation.boundedVars());
    final List<UTerm> subTerms = summation.body().subTerms();
    if (!(summation.body() instanceof UMul) || (subTerms.size() == 1))
      return expr;
    for (UVar boundedVar : boundedVars) {
      final Map<UTerm, UTerm> replacedTermsMap = new HashMap<>();
      final List<Value> varSchema = translator.getTupleVarSchema(boundedVar);
      for (Value v : varSchema) {
        final UVarTerm targetProjVarTerm = UVarTerm.mk(translator.mkProjVar(v, boundedVar));
        final UTerm replacedTerm;
        if ((replacedTerm = searchVarTermReplacement(targetProjVarTerm, summation)) != null) {
          replacedTermsMap.put(targetProjVarTerm, replacedTerm);
        }
      }
      if (replacedTermsMap.isEmpty())
        continue;
      // [a(t1) = a(t2)] => IsNull(a(t2))
      for (var pair : replacedTermsMap.entrySet()) {
        final UPred targetPred = (UPred) pair.getValue();
        if (isNullPred(targetPred)) {
          USum tmp = (USum) propagateNullValue(summation, pair.getKey());
          if (!tmp.equals(summation)) {
            isModified = true;
            summation = tmp;
          }
        }
      }
    }

    return summation;
  }

  private boolean isOutAggVar(UTerm t) {
    if (t == null)
      return false;
    if (t instanceof UVarTerm)
      return t.toString().contains(tail(translator.visibleVars).toString());
    else
      return false;
  }

  private UTerm aggResultNotNull(UTerm expr) {
    expr = transformSubTerms(expr, this::aggResultNotNull);
    UKind kind = expr.kind();
    if (kind != PRED) return expr;

    UPred pred = (UPred) expr;
    if (pred.isPredKind(EQ)) {
      UTerm op1 = pred.args().get(0);
      UTerm op2 = pred.args().get(1);
      if (op1 instanceof UVarTerm && isOutAggVar(op1) && op2.kind() == SUMMATION)
        return UMul.mk(expr, UNeg.mk(UPred.mkFunc(UName.NAME_IS_NULL, op1)));
    }
    return expr;
  }


  /**
   * if t has only one column a, then all a(t) will be replaced by t
   */
  private UTerm removeUselessAttrSym(UTerm expr) {
    expr = transformSubTerms(expr, this::removeUselessAttrSym);
    UKind kind = expr.kind();
    if (kind != SUMMATION) return expr;

    USum summation = (USum) expr;
    final Set<UVar> boundedVars = new HashSet<>(summation.boundedVars());
    final List<UTerm> subTerms = summation.body().subTerms();
    for (UVar boundedVar : boundedVars) {
      final List<Value> varSchema = translator.getTupleVarSchema(boundedVar);
      if (varSchema.size() == 1) {
        Value v = varSchema.get(0);
        final UVarTerm targetProjVarTerm = UVarTerm.mk(translator.mkProjVar(v, boundedVar));
        summation = (USum) summation.replaceAtomicTerm(targetProjVarTerm, UVarTerm.mk(boundedVar));
        isModified = true;
      }
    }
    return summation;
  }

  // for a SUM, if its all subTerms don't use its boundedVar, then extract its subTerms to replace SUM
  private UTerm extractUnrelatedSumSubTerms(USum sum) {
    List<UTerm> subTerms = sum.body().subTerms();
    List<UTerm> newMulTerms = new ArrayList<>();
    List<UTerm> removedMulTerms = new ArrayList<>();
    for (UTerm subTerm : subTerms) {
      boolean useBoundedVar = false;
      if (all(sum.boundedVars(), v -> !subTerm.isUsing(v))) {
        removedMulTerms.add(subTerm);
        newMulTerms.add(subTerm);
      }
//          NaturalCongruence<UTerm> cong = buildNaturalCongruence(subTerms);
//          if (subTerm.kind() == PRED) {
//            UPred pred = (UPred) subTerm;
//            UTerm op0 = pred.args().get(0);
//            UTerm op1 = pred.args().get(1);
//            UTerm
//          }
    }
    if (newMulTerms.isEmpty() && removedMulTerms.isEmpty())
      return sum;
    subTerms.removeAll(removedMulTerms);
    newMulTerms.add(sum);
    isModified = true;
    return UMul.mk(newMulTerms);
  }

  // \sum{x1, x2}(f(x1) * g(x2)) -> \sum{x1}(f(x1)) * \sum{x2}(f(x2))
  private UTerm splitMultipleSumTerms(USum sum) {
    UTerm sumBody = sum.body();
    List<UTerm> newMulTerms = new ArrayList<>();
    HashMap<UVar, ArrayList<UTerm>> varToTerms = new HashMap<>();
    for (UVar var : sum.boundedVars()) {
      boolean isConsidered = true;
      for (UTerm subTerm : sumBody.subTerms()) {
        if (subTerm.isUsing(var))
          for (UVar otherVar : sum.boundedVars()) {
            if (otherVar.equals(var)) continue;
            if (subTerm.isUsing(otherVar)) {
              isConsidered = false;
            }
          }
      }
      if (!isConsidered) continue;

      ArrayList<UTerm> termsUseVar = new ArrayList<>();
      all(sumBody.subTerms(), t -> {if(t.isUsing(var)) termsUseVar.add(t); return true;} );
      if (!termsUseVar.isEmpty())
        varToTerms.put(var, termsUseVar);
    }

    USum leftSum = (USum) sum.copy();
    for (UVar v : varToTerms.keySet()) {
      newMulTerms.add(USum.mk(new HashSet(Set.of(v)), UMul.mk(varToTerms.get(v))));
      leftSum.body().subTerms().removeAll(varToTerms.get(v));
      leftSum.removeBoundedVar(v);
    }

    if (!leftSum.boundedVars().isEmpty() && !leftSum.body().subTerms().isEmpty())
      newMulTerms.add(leftSum);

    if (newMulTerms.size() == 1)
      return newMulTerms.get(0);

    return UMul.mk(newMulTerms);
  }

  /** \sum{x1, x2}(f(x1) * g(x2) * [a(x1) = b(x2)] * [a(x1) = CONST])
   * -> \sum{x1, x2}(f(x1) * g(x2) * [b(x2) = CONST] * [a(x1) = CONST])
   * -> \sum{x1}(f(x1) * [a(x1) = CONST]) * \sum{x2}(f(x2) * [b(x2) = CONST])
   * b doesn't need to be different with a
   * only considers the boundedVar is exactly 2
   * */
  private UTerm splitMultipleSumEQTerms(USum sum) {
    if (sum.boundedVars().size() != 2) return sum;
    UTerm sumBody = sum.body();
    List<UTerm> newMulTerms = new ArrayList<>();
    HashMap<UVar, ArrayList<UTerm>> varToTerms = new HashMap<>();
    HashMap<UVar, ArrayList<UTerm>> varToEQTerms = new HashMap<>();
    for (UVar var : sum.boundedVars()) {
      ArrayList<UTerm> termsUseVar = new ArrayList<>();
      ArrayList<UTerm> eqTermsUseVar = new ArrayList<>();
      for (UTerm subTerm : sumBody.subTerms()) {
        boolean isConsideredTerm = true;
        if (subTerm.isUsing(var)) {
          for (UVar otherVar : sum.boundedVars()) {
            if (otherVar.equals(var)) continue;
            if (subTerm.isUsing(otherVar)) {
              isConsideredTerm = false;
            }
          }
          if (isConsideredTerm) // term that only contains boundedVar
            termsUseVar.add(subTerm);
          else { // contains both boundedVars, check whether it is EQ term like [a(x1) = b(x2)]
            if (subTerm instanceof UPred && ((UPred) subTerm).isPredKind(EQ))
              eqTermsUseVar.add(subTerm);
          }
        }
      }
      if (!termsUseVar.isEmpty())
        varToTerms.put(var, termsUseVar);
      if (!eqTermsUseVar.isEmpty())
        varToEQTerms.put(var, eqTermsUseVar);
    }

    // check whether contains EQ const
    for (final UVar key : varToEQTerms.keySet()) {
      ArrayList<UTerm> eqTermsUseVar = varToEQTerms.get(key);

      if (eqTermsUseVar.size() == 0) continue;
      USum toSplitSum = (USum) sum.copy();
      for (final UTerm eqTerm : eqTermsUseVar) {
        UPred eqPred = (UPred) eqTerm;
        assert (eqPred.isPredKind(EQ) && eqPred.args().size() == 2);
        UTerm useVarTerm = eqPred.args().get(0).isUsing(key) ? eqPred.args().get(0) : eqPred.args().get(1);
//        UTerm theOtherTerm = eqPred.args().get(0).isUsing(key) ? eqPred.args().get(1):eqPred.args().get(0);
        if (useVarTerm.kind() != VAR)
          break;
        UVar projVar = ((UVarTerm) useVarTerm).var();
        if (!projVar.is(UVar.VarKind.PROJ)) // only consider PROJ situation
          break;
        UTerm tgtTerm;
        if ((tgtTerm = searchEQConstProjVar(projVar, varToTerms.get(key), sum.boundedVars())) != null) {
          for (UTerm subTerm : toSplitSum.body().subTerms()) {
            if (subTerm.equals(eqTerm)) {
              // change toSplitSum
              toSplitSum = (USum) toSplitSum.replaceAtomicTerm(subTerm, subTerm.replaceAtomicTerm(useVarTerm, tgtTerm));
              break;
            }
          }
        }
      }
      if (!toSplitSum.equals(sum)) {
        return splitMultipleSumTerms(toSplitSum);
      }
    }


    return sum;
  }

  // apply split summations
  private UTerm extractHandleManyCases(UTerm expr) {
    expr = extractUnrelatedSumSubTerms((USum) expr);
    if (expr instanceof USum) {
      expr = splitMultipleSumTerms((USum) expr);
      if (expr instanceof USum)
        expr = splitMultipleSumEQTerms((USum) expr);
    } else {
      List<UTerm> newMulList = new ArrayList<>();
      for (UTerm subTerm : expr.subTerms()) {
        if (subTerm instanceof USum) {
          UTerm newMul = null;
          newMul = splitMultipleSumTerms((USum) subTerm);
          if (newMul instanceof USum)
            newMul = splitMultipleSumEQTerms((USum) subTerm);
          newMulList.add(newMul);
        } else
          newMulList.add(subTerm);
      }
      expr = UMul.mk(newMulList);
    }
    return expr;
  }


  private UTerm extractorPreprocess(UTerm expr) {
    expr = transformSubTerms(expr, this::extractorPreprocess);
    UKind kind = expr.kind();
    if (kind != MULTIPLY) return expr;

    List<UTerm> subTerms = expr.subTerms();
    HashMap<UVar, UVar> mapping = new HashMap<>();
    UVar outVar = tail(translator.visibleVars);
    for (UTerm subTerm : subTerms) {
      if (subTerm.kind() != PRED) continue;
      UPred pred = (UPred) subTerm;
      if (pred.isPredKind(EQ)) {
        UTerm op0 = pred.args().get(0);
        UTerm op1 = pred.args().get(1);
        if (op0.kind() != VAR || op1.kind() != VAR)
          continue;
        if (op0.tupleProjectedFromFuncParam(outVar) && !op1.tupleProjectedFromFuncParam(outVar)) {
          mapping.put(((UVarTerm) op1).var(), ((UVarTerm) op0).var());
        } else if (op1.tupleProjectedFromFuncParam(outVar) && !op0.tupleProjectedFromFuncParam(outVar)) {
          mapping.put(((UVarTerm) op0).var(), ((UVarTerm) op1).var());
        }
      }
    }

    ArrayList<UTerm> newSubTerms = new ArrayList<>();
    for (UTerm subTerm : subTerms) {
      if (subTerm.kind() == PRED && subTerm.isUsing(outVar))
        newSubTerms.add(subTerm);
      else {
        UTerm newSubTerm = subTerm;
        for (UVar var : mapping.keySet())
          newSubTerm = newSubTerm.replaceVar(var, mapping.get(var), false);
        if (newSubTerm.kind() == PRED && ((UPred) newSubTerm).isTruePred(globalExpr) == 1) {
          continue;
        }
        newSubTerms.add(newSubTerm);
      }
    }

    return UMul.mk(newSubTerms);
  }


  private UTerm simplifySummations(UTerm expr) {
    expr = transformSubTerms(expr, this::simplifySummations);
    UKind kind = expr.kind();
    if (kind != SQUASH && kind != NEGATION) return expr;

    // TODO: simplify summations
    return expr;
  }

  // for SQUASH NEGATION PRED, apply extractHandleManyCases(split summations)
  private UTerm extractUnrelatedSumTerms(UTerm expr) {
    expr = transformSubTerms(expr, this::extractUnrelatedSumTerms);
    UKind kind = expr.kind();
    if (kind != SQUASH && kind != NEGATION && kind != PRED) return expr;

    if (kind == PRED) {
      UPred pred = (UPred) expr;
      if (!pred.isPredKind(EQ))
        return expr;
      UTerm op1 = pred.args().get(0);
      UTerm op2 = pred.args().get(1);
      if (op1.kind() == SUMMATION)
        op1 = extractHandleManyCases(op1);
      if (op2.kind() == SUMMATION)
        op2 = extractHandleManyCases(op2);
      ArrayList<UTerm> args = new ArrayList<>();
      args.add(op1);
      args.add(op2);
      return UPred.mk(EQ, UName.mk("="), args);
    }

    UTerm body = (kind == NEGATION) ? ((UNeg) expr).body() : ((USquash) expr).body();
    UTerm newBody = null;
    switch (body.kind()) {
      case SUMMATION: {
        newBody = extractHandleManyCases(body);
        break;
      }
      case ADD: {
        ArrayList<UTerm> newSubTerms = new ArrayList<>();
        for (UTerm subTerm : body.subTerms()) {
          if (subTerm.kind() == SUMMATION)
            newSubTerms.add(extractHandleManyCases(subTerm));
          else
            newSubTerms.add(subTerm);
        }
        newBody = UAdd.mk(newSubTerms);
        break;
      }
      default: newBody = body;
    }
    return (kind == NEGATION) ? UNeg.mk(newBody) : USquash.mk(newBody);
  }


  /**
   * [sum1 = sum2] => 1 when sum1.equals(sum2)
   */
  private UTerm removeSumEqPred(UTerm expr) {
    expr = transformSubTerms(expr, this::removeSumEqPred);
    if (expr.kind() != PRED) return expr;

    UPred pred = (UPred) expr;
    if (pred.isPredKind(EQ)) {
      UTerm op1 = pred.args().get(0);
      UTerm op2 = pred.args().get(1);
      if (op1.equals(op2))
        return UConst.one();
    }
    return expr;
  }

  /**
   * [a = '1'], a is integer => [a = 1]
   */
  private UTerm autoTypeConversion(UTerm expr) {
    expr = transformSubTerms(expr, this::autoTypeConversion);
    if (expr.kind() != PRED) return expr;

    UPred pred = (UPred) expr;
    if (pred.isPredKind(EQ)) {
      UTerm op1 = pred.args().get(0);
      UTerm op2 = pred.args().get(1);
      //at least one operand is constant or string
      if ((op1.kind() != STRING && op1.kind() != CONST) &&
              (op2.kind() != STRING && op2.kind() != CONST))
        return expr;

      UTerm cstTerm = (op1.kind() == STRING || op1.kind() == CONST) ? op1 : op2;
      UTerm tgtTerm = (op1.kind() == STRING || op1.kind() == CONST) ? op2 : op1;

      // they are both constant or string, return
      if (tgtTerm.kind() == STRING || tgtTerm.kind() == CONST)
        return expr;
      // if targetTerm is not VAR; or it is not PROJ VAR, return
      if (tgtTerm.kind() != VAR || !(((UVarTerm) tgtTerm).var()).is(UVar.VarKind.PROJ))
        return expr;

      // get table name and column name
      UVar tgtVar = ((UVarTerm) tgtTerm).var();
      String[] names = tgtVar.name().toString().split("\\.");

      // dont consider other cases
      if (names.length != 2)
        return expr;

      for (Table table : schema.tables()) {
        if (!Objects.equals(table.name(), names[0]))
          continue;

        // type conversion here
        switch (table.column(names[1]).dataType().category()) {
          case STRING:
            if (cstTerm.kind() != STRING)
              expr = expr.replaceAtomicTerm(cstTerm, UString.mk(String.valueOf(((UConst) cstTerm).value())));
            break;
          case INTEGRAL:
            if (cstTerm.kind() != CONST)
              try {
                expr = expr.replaceAtomicTerm(cstTerm, UConst.mk(Integer.parseInt(((UString) cstTerm).value())));
              } catch (NumberFormatException e) {
                // for this case, consider [a = 'test'] and a is INT => this predicates return 0
                expr = UConst.zero();
              }
            break;
          default:
            return expr;
        }
      }
    }
    return expr;
  }

  /**
   * [a = null], a is VAR => IsNULL(a)
   */
  private UTerm eqNullConversion(UTerm expr) {
    expr = transformSubTerms(expr, this::eqNullConversion);
    if (expr.kind() != PRED) return expr;

    UPred pred = (UPred) expr;
    if (pred.isPredKind(EQ)) {
      UTerm op1 = pred.args().get(0);
      UTerm op2 = pred.args().get(1);
      //two operands should be VAR and CONST
      if ((op1.kind() != VAR || op2.kind() != CONST) &&
              (op1.kind() != CONST || op2.kind() != VAR))
        return expr;

      UTerm cstTerm = (op1.kind() == CONST) ? op1 : op2;
      UTerm tgtTerm = (op1.kind() == CONST) ? op2 : op1;

      if (!cstTerm.equals(UConst.nullVal()))
        return expr;

      assert tgtTerm.kind() == VAR;

      isModified = true;

      return mkIsNullPred(tgtTerm);
    }
    return expr;
  }

  /** check whether a term is [a(t) = CONST], if it is, return CONST
   * TODO: need to consider non-const boundedVar,∑{x, y} means y is a CONST to x
   * */
  private UTerm isEQConstTerm(UTerm term, UVar tgtVar, Set<UVar> boundedVars) {
    if (term instanceof UPred pred && pred.isPredKind(EQ) && pred.isUsing(tgtVar)) {
      assert pred.args().size() == 2;
      UTerm firstArg = pred.args().get(0);
      UTerm secondArg = pred.args().get(1);
      UTerm srcTerm = (firstArg.isUsing(tgtVar)) ? firstArg : secondArg;
      UTerm tgtTerm = (firstArg.isUsing(tgtVar)) ? secondArg : firstArg;
      if (tgtTerm.isUsing(tgtVar)) return null;
      if (!srcTerm.kind().isTermAtomic()) return null;
      for (UVar boundedVar : boundedVars) {
        if (boundedVar.equals(tgtVar)) continue;
        if (tgtTerm.isUsing(boundedVar)) return null;
      }
      return tgtTerm;
    }
    return null;
  }

  /** check whether a term is [a(x) = b(y)], where x is target boundedVar and y is another boundedVar
   * if it is, return true
   * */
  private boolean isEQAnotherBoundedVar(UTerm term, UVar tgtVar, Set<UVar> boundedVars) {
    if (term instanceof UPred pred && pred.isPredKind(EQ) && pred.isUsing(tgtVar)) {
      assert pred.args().size() == 2;
      UTerm firstArg = pred.args().get(0);
      UTerm secondArg = pred.args().get(1);
      UTerm tgtTerm = (firstArg.isUsing(tgtVar)) ? secondArg : firstArg;
      for (UVar boundedVar : boundedVars) {
        if (boundedVar.equals(tgtVar)) continue;
        if (tgtTerm.isUsing(boundedVar)) return true;
      }
      return false;
    }
    return false;
  }

  // if term consist tgtVar, try to replace the term with tgtVar by varToEQTerms
  private UTerm replaceVarToEQTerm(ArrayList<UTerm> varToEQTerms, UVar tgtVar, UTerm term) {
    for (final UTerm varToEQTerm : varToEQTerms) {
      UPred pred = (UPred) varToEQTerm;
      UTerm srcTerm = pred.args().get(0).isUsing(tgtVar) ? pred.args().get(0) : pred.args().get(1);
      UTerm tgtTerm = pred.args().get(0).isUsing(tgtVar) ? pred.args().get(1) : pred.args().get(0);
      if (!term.equals(term.replaceAtomicTerm(srcTerm, tgtTerm))) {
        return term.replaceAtomicTerm(srcTerm, tgtTerm);
      }
    }
    return null;
  }

  /**
   * \sum{t}(f(t) * g(t)), g(t) can use EQ pred like [a(t) = CONST] to transform into g()
   * -> \sum{t}(f(t) * g())
   * */
  private UTerm transformSumUnrelatedTermsEQPred(UTerm expr) {
    expr = transformSubTerms(expr, this::transformSumUnrelatedTermsEQPred);
    if (expr.kind() != SUMMATION) return expr;
    if (((USum) expr).body().kind() != MULTIPLY) return expr;
    // only consider one boundedvar
//    if (((USum) expr).boundedVars().size() != 1) return expr;
    USum sum = (USum) expr;

    for (UVar boundedVar : sum.boundedVars()) {
      // first we collect the EQ const term that is related to the boundedVar
      ArrayList<UTerm> varToEQTerms = new ArrayList<>();
      for (final UTerm subTerm : sum.body().subTerms()) {
        if (isEQConstTerm(subTerm, boundedVar, sum.boundedVars()) != null)
          varToEQTerms.add(subTerm);
      }

      // replace every term, check whether it is unrelated
      USum newSum = (USum) sum.copy();
      for (UTerm subTerm : sum.body().subTerms()) {
        if (!varToEQTerms.contains(subTerm)) {
          // only consider EQ pred and negation(with body sum), further it should be changed
          // only replace EQ pred whose args are atomic term
          if ((subTerm.kind() == PRED && ((UPred) subTerm).isPredKind(EQ))
                  || (subTerm.kind() == NEGATION && ((UNeg) subTerm).body().kind() == SUMMATION))
            if(subTerm.kind() == PRED) {
              UTerm tgtTerm;
              if (!all(((UPred) subTerm).args(), t -> t.kind().isTermAtomic())) continue;
              if ((tgtTerm = replaceVarToEQTerm(varToEQTerms, boundedVar, subTerm)) != null) {
                newSum.body().subTerms().remove(subTerm);
                newSum.body().subTerms().add(tgtTerm);
                return extractUnrelatedSumSubTerms(newSum);
              }
            } else if (subTerm.kind() == NEGATION) {
              assert ((UNeg) subTerm).body().kind() == SUMMATION;
              USum tgtSum = (USum) ((UNeg) subTerm).body();
              for (final UTerm subTgtTerm : tgtSum.body().subTerms()) {
                if (subTgtTerm.kind() == PRED) {
                  UTerm tgtTerm;
                  if (!all(((UPred) subTgtTerm).args(), t -> t.kind().isTermAtomic())) continue;
                  if ((tgtTerm = replaceVarToEQTerm(varToEQTerms, boundedVar, subTgtTerm)) != null) {
                    tgtSum.body().subTerms().remove(subTgtTerm);
                    tgtSum.body().subTerms().add(tgtTerm);
                    expr = extractUnrelatedSumSubTerms(expr);
                    break;
                  }
                }
              }
            }
        }
      }

    }

    return expr;
  }

  /**
   * \sum{t}(f(t) * g()), which g() is EQPred or NEG
   * -> \sum{t}(f(t)) * g()
   */
  private UTerm extractUnrelatedSumSubTerms(UTerm expr) {
    expr = transformSubTerms(expr, this::extractUnrelatedSumSubTerms);
    if (expr.kind() != SUMMATION) return expr;
    if (((USum) expr).body().kind() != MULTIPLY) return expr;

    USum sum = (USum) expr;
    ArrayList<UTerm> newMulList = new ArrayList<>();
    boolean haveExtract = true;
    newMulList.add(sum);
    while (haveExtract) {
      haveExtract = false;
      for (final UTerm subTerm : sum.body().subTerms()) {
        boolean canExtract = true;
        for (final UVar boundedVar : sum.boundedVars()) {
          if (subTerm.isUsing(boundedVar)) canExtract = false;
        }
        if (canExtract) {
          sum.body().subTerms().remove(subTerm);
          newMulList.add(subTerm);
          haveExtract = true;
          break;
        }
      }
    }

    if (newMulList.size() == 1)
      return newMulList.get(0);

    if (newMulList.size() > 1)
      return UMul.mk(newMulList);

    return expr;
  }

  private boolean usesTableVar(UTerm expr, String tableName, UVar var) {
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

  private boolean useTableVar(UTerm expr, UVar var) {
    Schema schema = CASTSupport.schema;
    for (Table table : schema.tables()) {
      String tableName = table.name();
      if (usesTableVar(expr, tableName, var))
        return true;
    }
    return false;
  }

  private UTerm removeUselessBoundedVarWithSquash(USum summation) {
    UTerm expr = summation.copy();
//        boolean oldIsModified = isModified;
    USquash squashExpr = (USquash) summation.body().subTerms().get(0).copy();
//        squashExpr = (USquash) extractUnrelatedSumTerms(squashExpr);
//        isModified = oldIsModified;
    USum newSum = (USum) USum.mk(summation.boundedVars(), squashExpr.body()).copy();
    UTerm tmp = removeUselessBoundedVar(newSum);
    if (isModified == false) {
      if (summation.boundedVars().size() == 1 && squashExpr.body().kind() == SUMMATION) {
        USum innerSum = (USum) squashExpr.body();
        UVar var = new ArrayList<>(summation.boundedVars()).get(0);
        NaturalCongruence<UTerm> cong = buildNaturalCongruence(innerSum.body().subTerms());
        final List<Value> varSchema = translator.getTupleVarSchema(var);
        ArrayList<Value> finalSchema = new ArrayList<>();
        for (Value attr : varSchema) {
          final UVarTerm targetProjVarTerm = UVarTerm.mk(translator.mkProjVar(attr, var));
          Set<UTerm> eqTuples = cong.eqClassOf(targetProjVarTerm);
          UTerm replaceTerm = null;
          for (UTerm term : eqTuples) {
            if (term.kind() == VAR && term.isUsing(tail(translator.visibleVars))) {
              replaceTerm = term;
              break;
            }
          }
          if (replaceTerm == null) {
            finalSchema.add(attr);
          } else {
            // replaceTerm should not replace the NaturalCongruence term
            innerSum = (USum) innerSum.replaceAtomicTermExcept(targetProjVarTerm, replaceTerm,
                    UPred.mkBinary(EQ, targetProjVarTerm, replaceTerm));
            isModified = true;
          }
        }
        translator.putTupleVarSchema(var, finalSchema);
        if (finalSchema.isEmpty())
          return USquash.mk(innerSum);
        else
          return USum.mk(summation.boundedVars(), USquash.mk(innerSum));
//            return expr;
      } else {
        return expr;
      }
    }

    if (tmp instanceof USum) {
      UTerm finalTmp = tmp;
      if (any(summation.boundedVars(), v -> ((USum) finalTmp).boundedVars().contains(v))) {
        return USum.mk(((USum) tmp).boundedVars(), USquash.mk(UExprSupport.normalizeExpr(((USum) tmp).body())));
      }
    }
    tmp = UExprSupport.normalizeExpr(tmp);
    return USquash.mk(tmp);
  }


  /**
   * \sum{t}[t = e] * f(t) => f(e)
   */
  private UTerm removeUselessBoundedVar(UTerm expr) {
    expr = transformSubTerms(expr, this::removeUselessBoundedVar);
    if (expr.kind() != SUMMATION) return expr;

    USum summation = (USum) expr;
    if (summation.body().subTerms().size() == 1
            && summation.body().subTerms().get(0).kind() == SQUASH
    ) {
      return removeUselessBoundedVarWithSquash(summation);
    }

    final Set<UVar> boundedVars = new HashSet<>(summation.boundedVars());
    final List<UTerm> subTerms = summation.body().subTerms();
    if (!(summation.body() instanceof UMul) || (subTerms.size() == 1))
      return expr;

    for (UVar boundedVar : boundedVars) {
      // only consider the boundedVar dont have R(t)
      if (useTableVar(summation.body(), boundedVar)) continue;
      final Map<UTerm, UTerm> replacedTermsMap = new HashMap<>();
      ArrayList<Value> cannotReplaceAttr = new ArrayList<>();
      final List<Value> varSchema = translator.getTupleVarSchema(boundedVar);
      for (Value v : varSchema) {
        final UVarTerm targetProjVarTerm = UVarTerm.mk(translator.mkProjVar(v, boundedVar));
        final UTerm replacedTerm;
        if ((replacedTerm = searchVarTermReplacement(targetProjVarTerm, summation)) != null) {
          replacedTermsMap.put(targetProjVarTerm, replacedTerm);
        } else {
          cannotReplaceAttr.add(v);
        }
      }
      if (replacedTermsMap.isEmpty())
        continue;
      // Special case for `[IsNull(t)]`
      if (all(replacedTermsMap.values(), UExprSupport::isNullPred)
              && cannotReplaceAttr.isEmpty()
              && all(subTerms,
              t -> replacedTermsMap.containsValue(t) || !t.isUsing(boundedVar) || canReplaceNullVar(t, boundedVar))) {
        for (UTerm repTerm : replacedTermsMap.values())
          summation = (USum) summation.replaceAtomicTerm(repTerm, UConst.one());
        ArrayList<UTerm> newSubTerms = new ArrayList<>();
        newSubTerms.addAll(summation.body().subTerms());
        for (UTerm subterm : newSubTerms) {
          if (subterm.isUsing(boundedVar) && canReplaceNullVar(subterm, boundedVar)) {
            UTerm newTerm = afterReplaceNullVar(subterm, boundedVar);
            summation = (USum) summation.replaceTerm(subterm, newTerm);
          }
        }
        summation.removeBoundedVar(boundedVar);
        isModified = true;
        continue;
      }
      // Common case, replace each projVar with corresponding substitutions
      for (var pair : replacedTermsMap.entrySet()) {
        final UPred targetPred = (UPred) pair.getValue();
        if (isNullPred(targetPred)) {
          summation = (USum) propagateNullValue(summation, pair.getKey());
          summation = (USum) summation.replaceAtomicTerm(targetPred, UConst.one());
          for (var otherPair : replacedTermsMap.entrySet()) {
            if (otherPair != pair) {
              replacedTermsMap.put(otherPair.getKey(), otherPair.getValue().replaceAtomicTerm(targetPred, UConst.one()));
            }
          }
        } else if (targetPred.isPredKind(EQ)) {
          assert targetPred.args().size() == 2;
          final UTerm targetProjVarTerm = pair.getKey();
          final UTerm predArg0 = targetPred.args().get(0), predArg1 = targetPred.args().get(1);
          final UTerm replaceTerm = targetProjVarTerm.equals(predArg0) ? predArg1 : predArg0;
          summation = (USum) summation.replaceAtomicTerm(targetPred, UConst.one());
          if (replaceTerm.kind() == SUMMATION)
            summation = (USum) replaceAtomicTermWithSummation(summation, targetProjVarTerm, replaceTerm);
          else
            summation = (USum) summation.replaceAtomicTerm(targetProjVarTerm, replaceTerm);
          updateReplacedTermsMap(replacedTermsMap, targetProjVarTerm, replaceTerm);
        }
      }
      if (cannotReplaceAttr.isEmpty())
        summation.removeBoundedVar(boundedVar);
      else
        translator.putTupleVarSchema(boundedVar, cannotReplaceAttr);
      isModified = true;
    }

    if (summation.boundedVars().isEmpty()) return summation.body();
    return summation;
  }

  /**
   * \sum{t}[t = a] * [a = e] * f(t) => f(e) * [a = e] (e is a constant)
   */
  private UTerm removeUselessInferenceBoundedVar(UTerm expr) {
    expr = transformSubTerms(expr, this::removeUselessInferenceBoundedVar);
    if (expr.kind() != SUMMATION) return expr;

    USum summation = (USum) expr;
    final Set<UVar> boundedVars = new HashSet<>(summation.boundedVars());
    final List<UTerm> subTerms = summation.body().subTerms();
    final NaturalCongruence<UVarTerm> eqVarClass = NaturalCongruence.mk();
    updateVarCongruenceInTermsPred(eqVarClass, summation.body(), summation);
    for (UVar boundedVar : boundedVars) {
      if (useTableVar(summation.body(), boundedVar)) continue;
      final Map<UTerm, UTerm> replacedTermsMap = new HashMap<>();
      List<Value> varSchema = translator.getTupleVarSchema(boundedVar);
      boolean replacedFlag = true;
      for (Value v : varSchema) {
        final UVarTerm targetProjVarTerm = UVarTerm.mk(translator.mkProjVar(v, boundedVar));
        final Set<UVarTerm> eqVars = eqVarClass.eqClassOf(targetProjVarTerm);
        if (eqVars.size() == 0) {
          replacedFlag = false;
          break;
        }
        boolean exist = false;
        for (UVarTerm checkVar : eqVars) {
          // invariant: only projvar
//              final UVarTerm checkProjVarTerm = UVarTerm.mk(mkProjVar(v, checkVar));
          final UVarTerm checkProjVarTerm = checkVar;
//              assert targetProjVarTerm.var().kind() == UVar.VarKind.PROJ && checkProjVarTerm.var().kind() == UVar.VarKind.PROJ;
          if (!checkProjVarTerm.equals(targetProjVarTerm) && canReplaceVarTerm(targetProjVarTerm, checkProjVarTerm, summation)) {
            replacedTermsMap.put(targetProjVarTerm, checkProjVarTerm);
            exist = true;
            break;
          }
        }
        if (!exist) {
          replacedFlag = false;
          break;
        }
      }
      if (!replacedFlag)
        continue;
      for (var pair : replacedTermsMap.entrySet()) {
        final UTerm replaceProjVarTerm = (UVarTerm) pair.getValue();
        final UTerm targetProjVarTerm = pair.getKey();
        summation = (USum) summation.replaceAtomicTerm(targetProjVarTerm, replaceProjVarTerm);
      }
      summation.removeBoundedVar(boundedVar);
      isModified = true;
      break;
    }
    if (summation.boundedVars().isEmpty()) return summation.body();
    return summation;
  }

  private void updateVarCongruenceInTermsPred(NaturalCongruence<UVarTerm> eqVarClass, UTerm tgtTerm, UTerm sumTerm) {
    if (tgtTerm.kind() == PRED
            && ((UPred) tgtTerm).isPredKind(EQ)
            && UExprSupport.isCriticalValue(tgtTerm, sumTerm))
      getEqVarCongruenceInTermsOfPred(eqVarClass, tgtTerm);
    for (UTerm subTerm : tgtTerm.subTerms())
      updateVarCongruenceInTermsPred(eqVarClass, subTerm, sumTerm);
  }

  private boolean canReplaceVarTerm(UVarTerm tgtProjVarTerm, UVarTerm chkProjVarTerm, UTerm term) {
//        assert sumTerm.kind() == SUMMATION && ((USum) sumTerm).boundedVars().contains(tgtProjVarTerm);
    // First case: two var is both boundedVar
//        assert tgtProjVarTerm.var().kind() == UVar.VarKind.PROJ && chkProjVarTerm.var().kind() == UVar.VarKind.PROJ;
    if (term.kind() == SUMMATION) {
      USum summation = (USum) term;

      if(summation.boundedVars().contains(tgtProjVarTerm.var().args()[0])
              && summation.boundedVars().contains(chkProjVarTerm.var().args()[0]))  return true;

      if (summation.boundedVars().contains(tgtProjVarTerm.var().args()[0])
              && !summation.boundedVars().contains(chkProjVarTerm.var().args()[0]))
        return findTargetTerm(chkProjVarTerm, summation.body());

      if (!summation.boundedVars().contains(tgtProjVarTerm.var().args()[0])
              && summation.boundedVars().contains(chkProjVarTerm.var().args()[0])) return false;

    }

    for (UTerm subTerm : term.subTerms()) {
      if (!canReplaceVarTerm(tgtProjVarTerm, chkProjVarTerm, subTerm)) return false;
    }
    return true;
  }

  private boolean findTargetTerm(UVarTerm chkProjVarTerm, UTerm term) {
    if (term.kind() == SUMMATION) {
      USum summation = (USum) term;
      if (summation.boundedVars().contains(chkProjVarTerm.var().args()[0])) return false;
    }

    for (UTerm subTerm : term.subTerms()) {
      if (!findTargetTerm(chkProjVarTerm, subTerm)) return false;
    }

    return true;
  }

  private void updateReplacedTermsMap(Map<UTerm, UTerm> replacedTermsMap, UTerm target, UTerm replace) {
    for (var pair : replacedTermsMap.entrySet()) {
      UTerm curTerm = pair.getValue();
      if (curTerm instanceof UMul) {
        UTerm replaceTerm = curTerm.replaceAtomicTerm(target, replace);
        replacedTermsMap.put(pair.getKey(), replaceTerm);
      } else if (curTerm instanceof UPred) {
        final UPred targetPred = (UPred) curTerm;
        if (!targetPred.isPredKind(EQ)) continue;

        assert targetPred.args().size() == 2;
        final UTerm targetProjVarTerm = pair.getKey();
        final UTerm predArg0 = targetPred.args().get(0), predArg1 = targetPred.args().get(1);
        UTerm replaceTerm = targetProjVarTerm.equals(predArg0) ? predArg1 : predArg0;
        if (targetProjVarTerm.equals(target) && replaceTerm.equals(replace)) continue;
        replaceTerm = replaceTerm.replaceAtomicTerm(target, replace);
        replacedTermsMap.put(
                targetProjVarTerm, UPred.mkBinary(EQ, targetProjVarTerm, replaceTerm));
      } else if (curTerm instanceof UVarTerm) {
        ;
      } else {
        assert false;
      }
    }
  }

  private UTerm replaceAtomicTermWithSummation(UTerm expr, UTerm base, UTerm rep) {
    assert base.kind().isTermAtomic();
    expr = transformSubTerms(expr, t -> replaceAtomicTermWithSummation(t, base, rep));
    if (!expr.equals(base)) return expr.copy();

    if (rep.kind() == SUMMATION) return translator.replaceAllBoundedVars(rep).copy();
    return rep.copy();
  }

  // Functions for searching for replacement of value of a projVar of a certain bounded var
  private UTerm searchVarTermReplacement(UVarTerm targetVar, USum summation) {
    // For a(t), if exists `[a(t) = a'(t')]` in summation, return `[a(t) = a'(t')]`
    // First check outermost-level subTerms of summation
    for (UTerm subTerm : summation.body().subTerms()) {
      if (canExtractVarTermReplacement(targetVar, subTerm)) {
        return subTerm.copy();
      }
    }
    // Second check whether exist natural congruence
    if (summation.body().kind() == MULTIPLY) {
      NaturalCongruence<UTerm> congruence = UExprSupport.getEqVarConstCongruenceInTermsOfMul(summation.body());
      Set<UTerm> targets = congruence.eqClassOf(targetVar);
      // consider all constant relative to targetVar
      final UTerm target = linearFind(targets, t -> t.kind() == CONST
              || (targetVar.var().kind() == UVar.VarKind.BASE && t.kind() == VAR && !t.isUsing(targetVar.var()))
              || (targetVar.var().kind() == UVar.VarKind.PROJ && t.kind() == VAR && !t.isUsing(targetVar.var().args()[0])));
      if (target != null)
        return UPred.mkBinary(EQ, targetVar, target);
    }
    // Then dig into lower-level terms
    return searchVarTermInnerReplacement(targetVar, summation);
  }

  private UTerm searchVarTermInnerReplacement(UVarTerm targetVar, USum ctx) {
    return searchVarTermInnerReplacement0(targetVar, ctx.body(), ctx, Collections.emptySet());
  }

  private UTerm searchVarTermInnerReplacement0(UVarTerm targetVar, UTerm currTerm, UTerm ctx, Set<UVar> innerBoundedVars) {
    final Set<UVar> innerBoundedVars0 = new HashSet<>(innerBoundedVars);
    if (currTerm.kind() == SUMMATION) innerBoundedVars0.addAll(((USum) currTerm).boundedVars());

    // atom
    if (currTerm.kind().isTermAtomic()) {
      if (canExtractVarTermReplacement(targetVar, currTerm) &&
              UExprSupport.isCriticalValue(currTerm, ctx) &&
              all(innerBoundedVars0, v -> !currTerm.isUsing(v)))
        return currTerm.copy();
      else return null;
    }

    // should not dig into negation
    if (currTerm.kind() == NEGATION) return null;

    // multiplication
    if (currTerm.kind() == MULTIPLY) {
      NaturalCongruence<UTerm> congruence = UExprSupport.getEqVarConstCongruenceInTermsOfMulCritical(currTerm, ctx);
      Set<UTerm> targets = congruence.eqClassOf(targetVar);
      // consider all constant relative to targetVar
      final UTerm target = linearFind(targets, t -> t.kind() == CONST
              || (targetVar.var().kind() == UVar.VarKind.BASE
                  && t.kind() == VAR
                  && !t.isUsing(targetVar.var())
                  && all(innerBoundedVars, v -> !t.isUsing(v)))
              || (targetVar.var().kind() == UVar.VarKind.PROJ
                  && t.kind() == VAR
                  && !t.isUsing(targetVar.var().args()[0])
                  && all(innerBoundedVars, v -> !t.isUsing(v))));
      if(target != null &&
         all(innerBoundedVars0, v -> !target.isUsing(v)))
        return UPred.mkBinary(EQ, targetVar, target);
    }

    UTerm targetTerm;
    for (UTerm subTerm : currTerm.subTerms()) {
      targetTerm = searchVarTermInnerReplacement0(targetVar, subTerm, ctx, innerBoundedVars0);
      if (targetTerm != null) return targetTerm.copy();
    }
    return null;
  }

  private boolean canExtractVarTermReplacement(UVarTerm targetVar, UTerm targetTerm) {
    if (targetTerm.kind() != PRED) return false;
    final UPred pred = (UPred) targetTerm;
    if (pred.isPredKind(EQ) && pred.args().contains(targetVar)) {
      assert pred.args().size() == 2;
      final UTerm arg0 = pred.args().get(0), arg1 = pred.args().get(1);
      final UTerm replaceVar = targetVar.equals(arg0) ? arg1 : arg0;
      final Set<UVar> targetBaseVars = UVar.getBaseVars(targetVar.var());
      // TODO: make replaceVar not using any targetBaseVars
      if (replaceVar.kind() == VAR && any(targetBaseVars, replaceVar::isUsing)) return false;
      return true;
    } else if (isNullPred(pred) && pred.args().get(0).equals(targetVar)) {
      return true;
    }
    return false;
  }

  // Functions for propagating IsNull(a(t)) to other terms' values
  private UTerm propagateNullValue(UTerm expr, UTerm nullVarTerm) {
    expr = transformSubTerms(expr, e -> propagateNullValue(e, nullVarTerm));
    if (expr.kind() != PRED) return expr;

    final UPred pred = (UPred) expr;
    if (!pred.isBinaryPred() || !pred.args().contains(nullVarTerm)) return expr;

    if (pred.isPredKind(EQ)) {
      // Case 1. If having `[IsNull(a(t))]`, then `[a(t) = a'(t')]` -> [IsNull(a'(t'))]
      assert pred.args().size() == 2;
      final UTerm predArg0 = pred.args().get(0), predArg1 = pred.args().get(1);
      final UTerm targetArg = nullVarTerm.equals(predArg0) ? predArg1 : predArg0;
      return mkIsNullPred(targetArg);
    } else {
      // Case 2. If having `[IsNull(a(t))]`, then `[a(t) > a'(t')]` -> 0
      return UConst.zero();
    }
  }

  /**
   * [IsNull(1)] -> 0, [IsNull(\sum(..))] -> 0, [IsNull(null)] -> 1 *
   */
  private UTerm removeIsNullPredOnValue(UTerm expr) {
    expr = transformSubTerms(expr, this::removeIsNullPredOnValue);
    if (expr.kind() != PRED || !isNullPred(expr)) return expr;

    assert ((UPred) expr).args().size() == 1;
    final UTerm predArg = ((UPred) expr).args().get(0);
    if (predArg.kind() != VAR) {
      isModified = true;
      return predArg.equals(UConst.NULL) ? UConst.one() : UConst.zero();
    } else if (notNullTerms.contains(predArg)) {
      isModified = true;
      return UConst.zero();
    }
    return expr;
  }

  /** Whether pred is like [funcName(...) > 0] */
  private boolean isPositiveFuncPred(UPred pred, String funcName) {
    if (!pred.isPredKind(GT)) return false;
    if (pred.args().get(1) instanceof UConst cst && cst.value() == 0
            && pred.args().get(0) instanceof UFunc func) {
      return Objects.equals(func.funcName().toString(), funcName);
    }
    return false;
  }

  private Set<UTerm> getNonNullArgsFromFuncPred(UPred pred) {
    // Each entry {func->list} of this map tells positions of non-null arguments of a function
    //   e.g. {like_op -> [0]} means that [like_op(a, b) > 0] implies
    //   that the 0-th argument of like_op (i.e. "a") should be non-null
    Map<String, int[]> positiveInfersNonNullArgs = new HashMap<>();
    positiveInfersNonNullArgs.put(PredefinedFunctions.NAME_LIKE, new int[]{0});

    Set<UTerm> nonNullArgs = new HashSet<>();
    for (Map.Entry<String, int[]> entry : positiveInfersNonNullArgs.entrySet()) {
      String funcName = entry.getKey();
      int[] nonNullArgsPos = entry.getValue();
      if (isPositiveFuncPred(pred, funcName)) {
        UFunc func = (UFunc) pred.args().get(0);
        List<UTerm> args = func.args();
        for (int argPos : nonNullArgsPos) nonNullArgs.add(args.get(argPos));
      }
    }
    return nonNullArgs;
  }

  /**
   * If having [a(t) > e] or [a(t) > a'(t')] or [a(t) = e]
   * -> [IsNull(a(t))] = 0 <br/>
   * Some arguments in function predicates (e.g. [like_op(a,b) > 0])
   * are also non-null.
   */
  private UTerm inferIsNullPredResult(UTerm expr) {
    expr = transformSubTerms(expr, this::inferIsNullPredResult);
    if (expr.kind() != MULTIPLY) return expr;
    final Set<UVarTerm> notNullVarTerms = new HashSet<>();

    // predicates
    final List<UTerm> predSubTerms = expr.subTermsOfKind(PRED);
    for (UTerm subTerm : predSubTerms) {
      final UPred pred = (UPred) subTerm;
      if (!pred.isBinaryPred()) continue;
      assert pred.args().size() == 2;
      final UTerm predArg0 = pred.args().get(0), predArg1 = pred.args().get(1);
      // ordinary binary predicates
      if (pred.isPredKind(EQ)) {
        if (predArg0.kind() == VAR && predArg1.kind() != VAR)
          notNullVarTerms.add((UVarTerm) predArg0);
        if (predArg0.kind() != VAR && predArg1.kind() == VAR) notNullVarTerms.add((UVarTerm) predArg1);
      } else {
        if (predArg0.kind() == VAR) notNullVarTerms.add((UVarTerm) predArg0);
        if (predArg1.kind() == VAR) notNullVarTerms.add((UVarTerm) predArg1);
      }
      // function predicates
      Set<UTerm> nonNullArgs = getNonNullArgsFromFuncPred(pred);
      for (UTerm arg : nonNullArgs) {
        if (arg.kind() == VAR) notNullVarTerms.add((UVarTerm) arg);
      }
    }

    final NaturalCongruence<UVar> eqVarClass = getEqVarCongruenceInTermsOfMul(expr);
    final Set<UVarTerm> notNullVarTermsExtend = new HashSet<>(notNullVarTerms);
    for (UVarTerm notNullVarTerm : notNullVarTerms) {
      final Set<UVar> eqVars = eqVarClass.eqClassOf(notNullVarTerm.var());
      notNullVarTermsExtend.addAll(map(eqVars, UVarTerm::mk));
    }
    for (UVarTerm notNullVarTerm : notNullVarTermsExtend) {
      final UTerm originalExpr = expr.copy();
      expr = expr.replaceAtomicTerm(mkIsNullPred(notNullVarTerm), UConst.zero());
      if (!originalExpr.equals(expr)) isModified = true;
    }

    return expr;
  }

  private static UTerm findNegationSummationPattern(UNeg negation, USquash squash) {
    if (negation.body().kind() != SUMMATION || squash.body().kind() != SUMMATION)
      return null;
    if (((USum) negation.body()).boundedVars().size() != 1 || ((USum) squash.body()).boundedVars().size() != 1)
      return null;
    if (((USum) negation.body()).body().kind() != MULTIPLY || ((USum) squash.body()).body().kind() != MULTIPLY)
      return null;

    final UMul negMul = (UMul) ((USum) negation.body()).body().copy();
    final UMul squMul = (UMul) ((USum) squash.body()).body().copy();
    final UVar negMulBoundedVar = (UVar) ((USum) negation.body()).boundedVars().toArray()[0];
    final UVar squMulBoundedVar = (UVar) ((USum) squash.body()).boundedVars().toArray()[0];
    final List<UTerm> negMulSubTerms = negMul.subTerms();
    final List<UTerm> squMulSubTerms = squMul.subTerms();
    final List<UTerm> negMulMaxMinSubTerms = new ArrayList<>();

    // find the [a(x14) < b(x16)] (or >)
    for (UTerm negMulSubTerm : negMulSubTerms) {
      if (negMulSubTerm.kind() == PRED &&
              (((UPred) negMulSubTerm).isPredKind(UPred.PredKind.LT) ||
                      ((UPred) negMulSubTerm).isPredKind(UPred.PredKind.GT))) {
        negMulMaxMinSubTerms.add(negMulSubTerm);
      }
    }

    if (negMulMaxMinSubTerms.size() != 1 || !negMulMaxMinSubTerms.get(0).isUsing(negMulBoundedVar)) return null;

    // first use replace var in args to prepare to generate correspond term
    final List<UTerm> negMulMaxMinArgs = ((UPred) negMulMaxMinSubTerms.get(0)).args();
    final List<UVarTerm> transformArgs = new ArrayList<>();
    assert negMulMaxMinArgs.size() == 2;
    for (UTerm varTerm : negMulMaxMinArgs) {
      if (varTerm.kind() != VAR)
        return null;
      UVarTerm tgtTerm = (UVarTerm) varTerm.copy();
      if (tgtTerm.isUsing(negMulBoundedVar))
        tgtTerm.replaceVarInplace(negMulBoundedVar, squMulBoundedVar, false);
      transformArgs.add(tgtTerm);
    }
    final UTerm squMulCorrespondTerm =
            UPred.mkBinary(EQ, transformArgs.get(0).var(), transformArgs.get(1).var());

    // then verify if the squMulSubTerms contain it
    if (!squMulSubTerms.contains(squMulCorrespondTerm))
      return null;

    // now need to verify other parts are equal
    final List<UTerm> negMulCopySubTerms = new ArrayList<>();
    final List<UTerm> squMulCopySubTerms = new ArrayList<>();
    for (UTerm negMulSubTerm : negMulSubTerms) {
      if (!negMulSubTerm.equals(negMulMaxMinSubTerms.get(0)))
        negMulCopySubTerms.add(negMulSubTerm.copy());
    }
    for (UTerm squMulSubTerm : squMulSubTerms) {
      if (!squMulSubTerm.equals(squMulCorrespondTerm))
        squMulCopySubTerms.add(squMulSubTerm.copy());
    }
    for (UTerm negMulCopySubTerm : negMulCopySubTerms) {
      negMulCopySubTerm.replaceVarInplace(negMulBoundedVar, squMulBoundedVar, false);
      if (!squMulCopySubTerms.contains(negMulCopySubTerm))
        return null;
    }
    for (UTerm squMulCopySubTerm : squMulCopySubTerms) {
      if (!negMulCopySubTerms.contains(squMulCopySubTerm))
        return null;
    }

    final UTerm result = USquash.mk(USum.mk(((USum) squash.body()).boundedVars(), UMul.mk(squMulCopySubTerms)));

    return result;
  }

  // whether tuple contains exactly one column
  // and vt refers to that column or the tuple
  private boolean isRefOfSingleColumnTuple(UVarTerm vt, UVar tuple) {
    List<Value> schema = translator.getTupleVarSchema(tuple);
    if (schema.size() != 1) return false;
    UVar v = vt.var();
    if (v.equals(tuple)) return true;
    Value column = schema.get(0);
    return v.kind() == UVar.VarKind.PROJ
            && v.name().toString().equals(column.toString());
  }

  private UTerm tableTermOf(UTerm term, UVar x1) {
    if (term instanceof UTable table && table.var().equals(x1))
      return term;
    return null;
  }

  // warning: [f(x1) op x] and [x op f(x1)] are both considered
  private UTerm comparisonWith(UTerm term, UVar x, UPred.PredKind op) {
    if (term instanceof UPred pred && pred.isPredKind(op)) {
      if (pred.args().get(0) instanceof UVarTerm vt
              && isRefOfSingleColumnTuple(vt, x))
        return pred.args().get(1);
      if (pred.args().get(1) instanceof UVarTerm vt
              && isRefOfSingleColumnTuple(vt, x))
        return pred.args().get(0);
    }
    return null;
  }

  // Given var "x", a binary operator "op" and term
  // ∑{x1}(r(x1) * p(x1) * [f(x1) op x]),
  // return [r(x1), p(x1), f(x1)]
  // Note: f is not necessarily a UFunc
  // Note: p is optional
  private UTerm[] extractFromComparisonInTable(UTerm term, UVar x, UPred.PredKind op) {
    if (term instanceof USum sum
            && sum.boundedVars().size() == 1
            && sum.body() instanceof UMul mul
            && mul.subTerms().size() >= 2) {
      List<UVar> bvs = new ArrayList<>(sum.boundedVars());
      UVar x1 = bvs.get(0);
      UTerm table = null, pred = null, func = null;
      // find r, p, f
      for (UTerm factor : mul.subTerms()) {
        // r(x1)
        UTerm tmp = tableTermOf(factor, x1);
        if (tmp != null && table == null) {
          table = tmp;
          continue;
        }
        // [f(x1) op x]
        tmp = comparisonWith(factor, x, op);
        if (tmp != null && func == null) {
          func = tmp;
          continue;
        }
        // others -> p(x1)
        pred = pred == null ? factor : UMul.mk(pred, factor);
      }
      if (table != null && func != null)
        return new UTerm[]{table, pred, func};
    }
    return null;
  }

  // Given value var "x" and term
  // not(∑{x1}(r(x1) * [f(x1) >/< x])),
  // return [r(x1), p(x1), f(x1)]
  // Note: p is optional
  private UTerm[] extractFromNoGTLTValueInTable(UTerm term, UVar x) {
    if (term instanceof UNeg neg) {
      UTerm[] res = extractFromComparisonInTable(neg.body(), x, GT);
      if (res != null) return res;
      return extractFromComparisonInTable(neg.body(), x, LT);
    }
    return null;
  }

  // Given value var "x" and term
  // ||∑{x1}(r(x1) * p(x1) * [f(x1) = x])||,
  // return [r(x1), p(x1), f(x1)]
  // Note: p is optional
  private UTerm[] extractFromExistsValueInTable(UTerm term, UVar x) {
    if (term instanceof USquash squash) {
      return extractFromComparisonInTable(squash.body(), x, EQ);
    }
    return null;
  }

  private boolean isZeroOneTerm(UTerm term) {
    if (term instanceof UConst cst) return cst.isZeroOneVal();
    if (term instanceof UMul mul) return all(mul.subTerms(), this::isZeroOneTerm);
    return term instanceof UPred
            || term instanceof UNeg
            || term instanceof USquash;
  }

  private UTerm[] extractFromUniqueMaxMin(UTerm not, UTerm squash, UVar x) {
    // match pattern
    UTerm[] res1 = extractFromNoGTLTValueInTable(not, x);
    if (res1 == null) return null;
    UTerm[] res2 = extractFromExistsValueInTable(squash, x);
    if (res2 == null) return null;
    // table names should equal
    UTable tableTerm1 = (UTable) res1[0];
    UTable tableTerm2 = (UTable) res2[0];
    UName table = tableTerm1.tableName();
    if (!table.equals(tableTerm2.tableName())) return null;
    UVar x1 = tableTerm1.var();
    UVar x2 = tableTerm2.var();
    // predicates should equal
    UTerm predTerm1 = res1[1];
    UTerm predTerm2 = res2[1];
    if (predTerm1 == null && predTerm2 != null
            || predTerm1 != null && predTerm2 == null)
      return null;
    if (predTerm1 != null && predTerm2 != null) {
      predTerm2 = predTerm2.replaceVar(x2, x1, false);
      if (!predTerm1.equals(predTerm2)) return null;
      // p should be a 0/1 value devoid of x
      if (predTerm1.isUsing(x)) return null;
      if (!isZeroOneTerm(predTerm1)) return null;
    }
    // functions should equal
    UTerm funcTerm1 = res1[2];
    UTerm funcTerm2 = res2[2];
    funcTerm2 = funcTerm2.replaceVar(x2, x1, false);
    if (!funcTerm1.equals(funcTerm2)) return null;
    // the function should not contain x
    if (funcTerm1.isUsing(x)) return null;
    // the function should not return null
    if (funcTerm1 instanceof USum
            || funcTerm1 instanceof USquash
            || funcTerm1 instanceof UNeg
            || funcTerm1 instanceof UPred) {
      return new UTerm[]{tableTerm1, predTerm1};
    }
    return null;
  }

  // Given var "x" and factors
  // not(∑{x1}(r(x1) * p(x1) * [f(x1) >/< x]))
  // and
  // ||∑{x2}(r(x2) * p(x2) * [f(x2) = x])||,
  // when f does not contain x and must not return null
  // and p is a 0/1 value devoid of x,
  // return [r(x1), p(x1)]
  // Note: p is optional; when p is absent, return [r(x1), null]
  private UTerm[] extractFromUniqueMaxMin(List<UTerm> factors, UVar x) {
    if (factors.size() != 2) return null;
    UTerm t1 = factors.get(0);
    UTerm t2 = factors.get(1);
    UTerm[] res = extractFromUniqueMaxMin(t1, t2, x);
    if (res != null) return res;
    return extractFromUniqueMaxMin(t2, t1, x);
  }

  /** ∑{x}(not(∑{x1}(r(x1) * p(x1) * [f(x1) >/< x]))
   *       * ||∑{x1}(r(x1) * p(x1) * [f(x1) = x])||)
   * ->
   * ||∑{x1}(r(x1) * p(x1)||
   * where f does not contain x and must not return null
   * and p is a 0/1 value devoid of x.
   * Note: p is optional
   */
  private UTerm simplifyUniqueMaxMin(UTerm term) {
    term = transformSubTerms(term, this::simplifyUniqueMaxMin);
    if (term instanceof USum sum && sum.body() instanceof UMul mul) {
      for (UVar x : sum.boundedVars()) {
        List<UTerm> subTerms = new ArrayList<>(mul.subTerms());
        // match pattern
        UTerm[] res = extractFromUniqueMaxMin(subTerms, x);
        if (res == null) continue;
        UTable table = (UTable) res[0].copy();
        UTerm newBody = res[1] == null ? table : UMul.mk(table, res[1].copy());
        // return ||∑{x1}(r(x1) * p(x1))||
        UVar x1 = table.var().copy();
        Set<UVar> boundVars = new HashSet<>();
        boundVars.add(x1);
        return USquash.mk(USum.mk(boundVars, newBody));
      }
    }
    return term;
  }

}
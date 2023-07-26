package wtune.superopt.logic;

import org.apache.commons.lang3.tuple.MutablePair;
import org.apache.commons.lang3.tuple.Pair;
import wtune.common.utils.NaturalCongruence;
import wtune.superopt.liastar.*;
import wtune.superopt.uexpr.*;

import java.lang.reflect.Array;
import java.util.*;
import java.util.stream.Collectors;

import static wtune.common.utils.IterableSupport.all;
import static wtune.common.utils.IterableSupport.any;
import static wtune.common.utils.SetSupport.filter;
import static wtune.superopt.liastar.Liastar.*;
import static wtune.superopt.uexpr.UExprSupport.*;
import static wtune.superopt.uexpr.UKind.*;
import static wtune.superopt.uexpr.UName.NAME_IS_NULL;

public class SqlSolverSupport {

  private HashMap<USum, String> sumVarMap = new HashMap<>();
  private final UTerm query1;
  private final UTerm query2;
  private final UVar outVar;
  private int uliaVarId = 0;

  public SqlSolverSupport(UTerm q1, UTerm q2, UVar v) {
    this.query1 = q1;
    this.query2 = q2;
    this.outVar = v;
  }

  public Liastar uexpToLiastar() {

    UTerm q1Lia = replaceSummations(sumVarMap, query1);
    UTerm q2Lia = replaceSummations(sumVarMap, query2);

    if (sumVarMap.isEmpty()) { // no summation
      return uexpWOSumToLiastar(q1Lia, q2Lia);
    } else {
      return uexpWithSumToLiastar(q1Lia, q2Lia);
    }
  }

  HashSet<UVar> initFreeTuples() {
    HashSet<UVar> result = new HashSet<>();
    if(outVar.kind() == UVar.VarKind.BASE) {
      result.add(outVar.copy());
    } else {
      result.addAll(List.of(outVar.args()));
    }
    return result;
  }

  Liastar uexpWithSumToLiastar(UTerm t1, UTerm t2) {
    HashMap<UTerm, String> termMap = new HashMap<>();
    Liastar result = Liastar.mkNot(false,
        Liastar.mkEq(false,
            transUexpWithoutSum(false, t1, termMap, new HashSet<>()),
            transUexpWithoutSum(false, t2, termMap, new HashSet<>())
        )
    );
    ArrayList<UTerm> sums = new ArrayList<>(sumVarMap.keySet());
    ArrayList<String> sumVars = new ArrayList<>();
    for (int i = 0; i < sums.size(); ++i) {
      sumVars.add(sumVarMap.get(sums.get(i)));
    }
    HashSet<UVar> freeTuples = initFreeTuples();
    result = Liastar.mkAnd(false, result,
        sumsToLiaStar(false, true, sums, sumVars, termMap, freeTuples)
    );
    result.prepareInnervector(new HashSet<>(result.collectVarSet()));
    if (LogicSupport.dumpLiaFormulas) {
      System.out.println("Lia* before simplification: " + result);
    }
    result.simplifyIte();
    return result;
  }

  private Liastar getOrRegisterLiaForUVar(UVar uVar, Map<UVar, String> uVarsToLiaVars) {
    assert uVar.isUnaryVar();
    Liastar baseLia = null;
    final UVar baseVar = UVar.getSingleBaseVar(uVar);
    for (UVar v : uVarsToLiaVars.keySet()) {
      if (baseVar.equals(v)) {
        final String varName = uVarsToLiaVars.get(v);
        baseLia = Liastar.mkVar(false, varName);
        break;
      }
    }
    if (baseLia == null) {
      final String varName = newUliaVarName();
      uVarsToLiaVars.put(baseVar, varName);
      baseLia = Liastar.mkVar(false, varName);
    }
    return uVar.is(UVar.VarKind.BASE) ?
        baseLia : Liastar.mkFunc(false, uVar.name().toString(), baseLia);
  }

  Liastar transUexpNoSum(UTerm exp, Map<UVar, String> uVarsToLiaVars) {
    switch (exp.kind()) {
      case SUMMATION -> {
        // should not have summation!"
        assert false;
        return null;
      }
      case ADD -> {
        Liastar result = null;
        final List<UTerm> subt = exp.subTerms();

        int constVal = 0;
        int i = 0;
        for(i = 0; i < subt.size(); ++ i) {
          UTerm cur = subt.get(i);
          if(cur instanceof UConst)
            constVal = constVal + ((UConst)cur).value();
          else
            break;
        }
        if(i == subt.size()) return mkConst(false, constVal);

        for (UTerm t : subt) {
          final Liastar curLia = transUexpNoSum(t, uVarsToLiaVars);
          if(curLia instanceof LiaconstImpl) {
            if( ((LiaconstImpl)curLia).getValue() == 0 )
              continue;
          }
          if (result == null) {
            result = curLia;
          } else {
            if (result instanceof LiaiteImpl) result = ((LiaiteImpl) result).plusIte(curLia);
            else if (curLia instanceof LiaiteImpl) result = ((LiaiteImpl) curLia).plusIte(result);
            else result = Liastar.mkPlus(false, result, curLia);
          }
        }
        return (result == null) ? mkConst(false, 0) : result;
      }
      case MULTIPLY -> {
        Liastar result = null;
        final List<UTerm> subt = exp.subTerms();
        for (UTerm t : subt) {
          final Liastar curLia = transUexpNoSum(t, uVarsToLiaVars);
          if(curLia instanceof LiaconstImpl) {
            long value = ((LiaconstImpl)curLia).getValue();
            if( value == 0 )
              return mkConst(false, 0);
            if(value == 1)
              continue;
          }
          if (result == null) result = curLia;
          else {
            if (result instanceof LiaiteImpl) result = ((LiaiteImpl) result).MultIte(curLia);
            else if (curLia instanceof LiaiteImpl) result = ((LiaiteImpl) curLia).MultIte(result);
            else result = Liastar.mkMult(false, result, curLia);
          }
        }
        return (result == null) ? mkConst(false, 1) : result;
      }
      case NEGATION -> {
        final UTerm body = ((UNeg) exp).body();
        final Liastar cond = Liastar.mkEq(false, transUexpNoSum(body, uVarsToLiaVars), Liastar.mkConst(false, 0));
        return Liastar.mkIte(false, cond, Liastar.mkConst(false, 1), Liastar.mkConst(false, 0));
      }
      case SQUASH -> {
        final UTerm body = ((USquash) exp).body();
        final Liastar cond = Liastar.mkEq(false, transUexpNoSum(body, uVarsToLiaVars), Liastar.mkConst(false, 0));
        return Liastar.mkIte(false, cond, Liastar.mkConst(false, 0), Liastar.mkConst(false, 1));
      }
      case CONST -> {
        return Liastar.mkConst(false, ((UConst) exp).value());
      }
      case TABLE -> {
        final UTable table = (UTable) exp;
        final String tblName = table.tableName().toString();
        final UVar tblVar = table.var();
        final Liastar lVar = getOrRegisterLiaForUVar(tblVar, uVarsToLiaVars);
        return Liastar.mkFunc(false, tblName, lVar);
      }
      case PRED -> {
        final UPred pred = (UPred) exp;
        if (pred.isPredKind(UPred.PredKind.FUNC) && isPredOfVarArg(pred)) {
          // Case 1. [p(a(t))]
          final List<UVar> pArgs = UExprSupport.getPredVarArgs(pred);
          assert pArgs.size() == 1;
          final UVar predVar = pArgs.get(0); // a(t)
          final String predName = pred.predName().toString();
          final Liastar lVar = getOrRegisterLiaForUVar(predVar, uVarsToLiaVars);
          final Liastar funcLia = Liastar.mkFunc(false, predName, lVar);
          return Liastar.mkIte(false,
              Liastar.mkEq(false, funcLia, Liastar.mkConst(false, 0)),
              Liastar.mkConst(false, 0),
              Liastar.mkConst(false, 1));
        } else if (pred.isBinaryPred()) {
          // Case 2. [U-expr0 <binary op> U-expr1]
          final Liastar liaVar0 = transUexpNoSum(pred.args().get(0), uVarsToLiaVars);
          final Liastar liaVar1 = transUexpNoSum(pred.args().get(1), uVarsToLiaVars);

          if(liaVar0 instanceof LiaconstImpl && liaVar1 instanceof LiaconstImpl) {
            long value0 = ((LiaconstImpl)liaVar0).getValue();
            long value1 = ((LiaconstImpl)liaVar1).getValue();
            boolean b = switch (pred.predKind()) {
              case EQ -> value0 == value1;
              case NEQ -> value0 != value1;
              case LE -> value0 <= value1;
              case LT -> value0 < value1;
              case GE -> value0 >= value1;
              case GT -> value0 > value1;
              default -> throw new IllegalArgumentException("unsupported predicate in Uexpr.");
            };
            return (b == true) ? mkConst(false, 1) : mkConst(false, 0);
          }

          final Liastar target = switch (pred.predKind()) {
            case EQ -> Liastar.mkEq(false, liaVar0, liaVar1);
            case NEQ -> Liastar.mkNot(false, Liastar.mkEq(false, liaVar0, liaVar1));
            case LE -> Liastar.mkLe(false, liaVar0, liaVar1);
            case LT -> Liastar.mkLt(false, liaVar0, liaVar1);
            case GE -> Liastar.mkLe(false, liaVar1, liaVar0);
            case GT -> Liastar.mkLt(false, liaVar1, liaVar0);
            default -> throw new IllegalArgumentException("unsupported predicate in Uexpr.");
          };
          return Liastar.mkIte(false, target,
              Liastar.mkConst(false, 1),
              Liastar.mkConst(false, 0));
        } else {
          throw new UnsupportedOperationException("unsupported UPred var type.");
        }
      }
      case VAR -> {
        return getOrRegisterLiaForUVar(((UVarTerm) exp).var(), uVarsToLiaVars);
      }
      case STRING -> {
        return Liastar.mkString(false, ((UString) exp).value());
      }
      default -> {
        throw new IllegalArgumentException("unsupported Uexpr type.");
      }
    }
  }

  Liastar uexpWOSumToLiastar(UTerm t1, UTerm t2) {
    final Map<UVar, String> varMap = new HashMap<>();
    return Liastar.mkNot(false, Liastar.mkEq(false, transUexpNoSum(t1, varMap), transUexpNoSum(t2, varMap)));
  }

  int newUliaVarId() {
    uliaVarId = uliaVarId + 1;
    return uliaVarId;
  }

  String newUliaVarName() {
    int id = newUliaVarId();
    return "u" + id;
  }

  void mergeSameSum(ArrayList<UTerm> sumList) {
    if (sumList.size() > 1) {
      for (int i = 0; i < sumList.size(); i++) {
        for (int j = i + 1; j < sumList.size(); j++) {
          if (sumList.get(i).equals(sumList.get(j))) {
            sumList.set(i, sumList.get(j).copy());
          }
        }
      }
    }
  }


  public static boolean overlap(HashSet<UVar> s1, HashSet<UVar> s2) {
    for(UVar v : s1) {
      if(s2.contains(v)) {
        return true;
      }
    }
    return false;
  }

  static ArrayList<HashSet<UVar>> buildEqRelation(Set<Pair<UVar, UVar>> eqVarPairs) {
    ArrayList<HashSet<UVar>> eqRels = new ArrayList<>();
    for(Pair<UVar, UVar> pair : eqVarPairs) {
      UVar v1 = pair.getLeft();
      UVar v2 = pair.getRight();
      HashSet<UVar> targetSet = null;
      for(int i = 0; i < eqRels.size(); ++ i) {
        HashSet<UVar> eqRel = eqRels.get(i);
        if(eqRel.contains(v1) || eqRel.contains(v2)) {
          if(targetSet == null) {
            targetSet = eqRel;
          } else {
            targetSet.addAll(eqRel);
            eqRel.clear();
          }
          targetSet.add(v1.copy());
          targetSet.add(v2.copy());
        }
      }
      if(targetSet == null) {
        HashSet<UVar> eqRel = new HashSet<>();
        eqRel.add(v1.copy());
        eqRel.add(v2.copy());
        eqRels.add(eqRel);
      }
    }

    ArrayList<HashSet<UVar>> result = new ArrayList<>();
    for(HashSet<UVar> s : eqRels) {
      if(!s.isEmpty()) {
        result.add(s);
      }
    }
    return result;
  }

  public static boolean hasFreeTuple(UVar v, HashSet<UVar> freeTuples) {
    switch (v.kind()) {
      case PROJ -> {
        for(UVar arg : v.args()) {
          if(hasFreeTuple(arg, freeTuples)) {
            return true;
          }
        }
        return false;
      }
      case BASE -> {
        return freeTuples.contains(v);
      }
      default -> {
        return false;
      }
    }
  }

  UVar selectMiniNameUVar(HashSet<UVar> vars) {
    UVar miniVar = null;
    for(UVar v : vars) {
      if (miniVar == null) {
        miniVar = v.copy();
      } else if (v.toString().compareTo(miniVar.toString()) < 0) {
        miniVar = v.copy();
      }
    }
    return miniVar;
  }


  int computeTargetTupleScoreForOneUTerm(UTerm expr, HashSet<UVar> curSet, UVar targetTuple, Set<UTerm> existingTerms) {
    switch (expr.kind()) {
      case TABLE: {
        UTable table = (UTable) expr;
        UName tableName = table.tableName();
        UVar innerTuple = table.var();
        if (curSet.contains(innerTuple)) {
          UTable newTable = UTable.mk(tableName, targetTuple);
          return (existingTerms.contains(newTable)) ? 1 : 0;
        } else {
          return 0;
        }
      }
      case NEGATION: {
        UNeg term = (UNeg) expr;
        return computeTargetTupleScoreForOneUTerm(term.body(), curSet, targetTuple, existingTerms);
      }
      case MULTIPLY: {
        UMul term = (UMul) expr;
        int result = 0;
        for(UTerm subterm : term.subTerms()) {
          result = result + computeTargetTupleScoreForOneUTerm(subterm, curSet, targetTuple, existingTerms);
        }
        return result;
      }
      case SQUASH: {
        USquash term = (USquash) expr;
        return computeTargetTupleScoreForOneUTerm(term.body(), curSet, targetTuple, existingTerms);
      }
      case PRED: {
        UPred pred = (UPred) expr;
        if (pred.isPredKind(UPred.PredKind.FUNC) && isPredOfVarArg(pred)) {
          // [p(a(t))]
          final List<UVar> pArgs = UExprSupport.getPredVarArgs(pred);
          assert pArgs.size() == 1;
          final UVar predVar = pArgs.get(0); // a(t)
          final UName predName = pred.predName();
          if (curSet.contains(predVar)) {
            List<UTerm> argList = new ArrayList<>();
            argList.add(UVarTerm.mk(targetTuple));
            UPred newPred = UPred.mk(UPred.PredKind.FUNC, predName, argList);
            if (existingTerms.contains(newPred)) {
              return 1;
            }
          }
        }
        return 0;
      }
      case ADD: {
        UAdd term = (UAdd) expr;
        int result = 0;
        for(UTerm subterm : term.subTerms()) {
          result = result + computeTargetTupleScoreForOneUTerm(subterm, curSet, targetTuple, existingTerms);
        }
        return result;
      }
      default: {
        return 0;
      }
    }
  }

  int computeScoreForTargetTuple(ArrayList<UTerm> sumList, HashSet<UVar> curSet, UVar targetTuple, Set<UTerm> existingTerms) {
    int result = 0;
    for(UTerm term : sumList) {
      result = result + computeTargetTupleScoreForOneUTerm(term, curSet, targetTuple, existingTerms);
    }
    return result;
  }

  UVar buildTargetTuplesForOneEqrel(ArrayList<UTerm> sumList, HashSet<UVar> curSet, HashSet<UVar> freeTuples, Set<UTerm> existingTerms) {
    HashSet<UVar> targetTuples = new HashSet<>();
    for(UVar v : curSet) {
      if(existingTerms.contains(UVarTerm.mk(v))) {
        targetTuples.add(v.copy());
      }
    }
    if(!targetTuples.isEmpty()) {
      int maxScore = -1;
      UVar targetTuple = null;
      for(UVar var : targetTuples) {
        int curScore = computeScoreForTargetTuple(sumList, curSet, var, existingTerms);
        if(curScore > maxScore) {
          targetTuple = var;
          maxScore = curScore;
        }
      }
      return targetTuple;
    }

    targetTuples = new HashSet<>();
    for(UVar v : curSet) {
      if(hasFreeTuple(v, freeTuples)) {
        targetTuples.add(v.copy());
      }
    }
    if(!targetTuples.isEmpty()) {
      int maxScore = -1;
      UVar targetTuple = null;
      for(UVar var : targetTuples) {
        int curScore = computeScoreForTargetTuple(sumList, curSet, var, existingTerms);
        if(curScore > maxScore) {
          targetTuple = var;
          maxScore = curScore;
        }
      }
      return targetTuple;
    }

    return selectMiniNameUVar(curSet);
  }

  ArrayList<UVar> buildTargetTuples(ArrayList<UTerm> sumList, ArrayList<HashSet<UVar>> eqRels, HashSet<UVar> freeTuples, Set<UTerm> existingTerms) {
    ArrayList<UVar> targetTuples = new ArrayList<>();
    for(int i = 0; i < eqRels.size(); ++ i) {
      HashSet<UVar> curSet = eqRels.get(i);
      targetTuples.add(buildTargetTuplesForOneEqrel(sumList, curSet, freeTuples, existingTerms));
    }
    return targetTuples;
  }

  void addEqSetToRels(ArrayList<HashSet<UVar>> eqRels, HashSet<UVar> newSet) {
    int i = 0;
    for( ; i < eqRels.size(); ++ i) {
      HashSet<UVar> curSet = eqRels.get(i);
      boolean succeed = false;
      for(UVar v : newSet) {
        if(curSet.contains(v)) {
          curSet.addAll(newSet);
          succeed = true;
          break;
        }
      }
      if(succeed == true)
        break;
    }
    if(i == eqRels.size()) {
      eqRels.add(newSet);
    }
  }

  void addVarToEqRel(ArrayList<HashSet<UVar>> eqRels, UVar v, Set<UTerm> existingTerms) {
    switch (v.kind()) {
      case PROJ -> {
        UName attrName = UName.mk(v.name().toString());
        UVar innerTuple = v.args()[0];
        for(int i = 0; i < eqRels.size(); ++ i) {
          HashSet<UVar> curSet = eqRels.get(i);
          if(curSet.contains(innerTuple)) {
            HashSet<UVar> newSet = new HashSet<>();
            newSet.add(v);
            for(UVar tuple : curSet) {
              UVar eqTuple = (tuple.kind() == UVar.VarKind.BASE) ? tuple.copy() : tuple.args()[0].copy();
              newSet.add(UVar.mkProj(attrName,eqTuple));
            }
            addEqSetToRels(eqRels, newSet);
            break;
          } else if (any(curSet, arg -> arg.isUsing(innerTuple))) {
            HashSet<UVar> newSet = new HashSet<>();
            newSet.add(v);
            for(UVar tuple : curSet) {
              UVar eqTuple = (tuple.kind() == UVar.VarKind.BASE) ? tuple.copy() : tuple.args()[0].copy();
              UVar newTuple = UVar.mkProj(attrName,eqTuple);
              if (existingTerms.contains(UVarTerm.mk(newTuple))) {
                newSet.add(newTuple);
              }
            }
            addEqSetToRels(eqRels, newSet);
            break;
          }
        }
        break;
      }
      default -> {
        break;
      }
    }
  }

  static void mergeEqRels(ArrayList<HashSet<UVar>> eqRels) {

    boolean modified = true;
    while(modified) {
      modified = false;
      for (int i = 0; i < eqRels.size(); ++i) {
        HashSet<UVar> thisSet = eqRels.get(i);
        if(thisSet == null) continue;

        for(int j = i + 1; j < eqRels.size(); ++ j) {
          HashSet<UVar> thatSet = eqRels.get(j);
          if(thatSet == null) continue;

          if(overlap(thisSet, thatSet)) {
            thisSet.addAll(thatSet);
            eqRels.set(i, thisSet);
            eqRels.set(j, null);
            modified = true;
          }
        }
      }
    }

    for(int i = 0; i < eqRels.size(); ++ i) {
      if(eqRels.get(i) == null) {
        eqRels.remove(i);
        i --;
      }
    }
  }

  void expandEqRelation(ArrayList<HashSet<UVar>> eqRels, ArrayList<UTerm> sumList, Set<UTerm> existingTerms) {
    HashSet<UVar> tuples = new HashSet<>();
    for(UTerm t : sumList) {
      tuples.addAll(searchFreeUnaryVars(t));
    }
    for(UVar v : tuples) {
      addVarToEqRel(eqRels, v, existingTerms);
    }

    mergeEqRels(eqRels);
  }

  void rewriteWithEqRelation(UTerm cur, ArrayList<HashSet<UVar>> eqRels, ArrayList<UVar> targetTuples) {
    for(int j = 0; j < eqRels.size(); ++ j) {
      HashSet<UVar> curSet = eqRels.get(j);
      UVar targetTuple = targetTuples.get(j);
      for(UVar v : curSet) {
        if(!v.equals(targetTuple)) {
          cur.replaceVarInplace(v, targetTuple, false);
        }
      }
    }
  }

  private boolean notisnullTerm(UTerm t) {
    if (t == null) return false;
    if (t.kind() == NEGATION) {
      UTerm body = ((UNeg) t).body();
      return isNullUTerm(body);
    }

    return false;
  }

  void rewriteSingleUTermWithEqRelation(UTerm cur, ArrayList<HashSet<UVar>> eqRels, ArrayList<UVar> targetTuples) {
    for(int j = 0; j < eqRels.size(); ++ j) {
      HashSet<UVar> curSet = eqRels.get(j);
      UVar targetTuple = targetTuples.get(j);
      for(UVar v : curSet) {
        if(!v.equals(targetTuple)) {
          if (cur.kind() == MULTIPLY) {
            UMul mul = (UMul) cur;
            List<UTerm> subterms = mul.subTerms();
            if (subterms.size() == 3) {
              UTerm t0 = subterms.get(0);
              UTerm t1 = subterms.get(1);
              UTerm t2 = subterms.get(2);
              if (   t0.kind() == TABLE
                  && t1.kind() == PRED
                  && ((UPred)t1).isPredKind(UPred.PredKind.EQ)
                  && notisnullTerm(t2))
                continue;
            }
          }
          cur.replaceVarInplaceWOPredicate(v, targetTuple);
        }
      }
    }
  }


  boolean allIsMult(ArrayList<UTerm> sumList) {
    for(UTerm t : sumList) {
      if(!(t instanceof UMul)) {
        return false;
      }
    }
    return true;
  }

  boolean isUsingTuples(UVar var, HashSet<UVar> freeTuples) {
    for(UVar v : freeTuples) {
      if(var.isUsing(v)) {
        return true;
      }
    }
    return false;
  }

  void rewriteSumsWithIndPred(ArrayList<UTerm> sumList, HashSet<UVar> freeTuples, Set<UTerm> existingTerms) {
    if(!allIsMult(sumList)) {
      return;
    }
    for(UTerm curExp : sumList) {
      Set<Pair<UVar, UVar>> eqVars = collectPredicatesFromOneTerm(curExp);
      UMul tmp = (UMul) curExp;
      for(UTerm term : tmp.subTerms()) {
        if(term instanceof UNeg) {
          term = ((UNeg) term).body();
        } else if(term instanceof USquash) {
          term = ((USquash) term).body();
        }
        if(!(term instanceof UPred))
          continue;
        UPred pred = (UPred) term;
        if (pred.isPredKind(UPred.PredKind.FUNC) && isPredOfVarArg(pred)) {
          for(Pair<UVar, UVar> pair : eqVars) {
            UVar left = pair.getLeft();
            UVar right = pair.getRight();
            if(isUsingTuples(left, freeTuples)) {
              pred.replaceVarInplace(right, left, false);
            } else {
              pred.replaceVarInplace(left, right, false);
            }
          }
        }
      }
    }
    return;
  }

  boolean instantiationWithPredicate(ArrayList<UTerm> sumList, HashSet<UVar> freeTuples, Set<UTerm> existingTerms) {

    ArrayList<HashSet<UVar>> eqRels = collectPredicates(sumList);
    mergeEqRels(eqRels);
//    if(eqRels.isEmpty())
//      rewriteSumsWithIndPred(sumList, freeTuples, existingTerms);
    if (eqRels.isEmpty() && (sumList.size() > 1)) {
      for(UTerm term : sumList) {
        ArrayList<UTerm> tmp = new ArrayList<>();
        tmp.add(term);
        instantiationWithPredicate(tmp, freeTuples, existingTerms);
      }
    }
    if(eqRels.isEmpty() && !allIsMult(sumList)) {
      return false;
    }
    expandEqRelation(eqRels, sumList, existingTerms);
    ArrayList<UVar> targetTuples = buildTargetTuples(sumList, eqRels, freeTuples, existingTerms);

    for (int i = 0; i < sumList.size(); ++i) {
      UTerm cur = sumList.get(i);
      if(sumList.size() == 1) {
        rewriteSingleUTermWithEqRelation(cur, eqRels, targetTuples);
      } else {
        rewriteWithEqRelation(cur, eqRels, targetTuples);
      }
    }
    // when there is only one summation, we still need to perform instantiation with tuple
    return (sumList.size() > 1);
  }

  boolean instantiationWithTuple(ArrayList<UTerm> sumList, UVar commonTuple, HashSet<UVar> freeTuples) {
    if(sumList.size() > 1)
      return false;
    for(UTerm t : sumList) {
      if(t instanceof USum) {
        return false;
      }
    }
    for(int i = 0; i < sumList.size(); ++ i) {
      sumList.set(i, instantiationOneSumWithTuple(sumList.get(i), commonTuple, freeTuples));
    }
    return true;
  }


  Set<UVar> collectBaseTuple(Set<UVar> tuples) {
    Set<UVar> baseTuples = new HashSet<>();
    for(UVar v : tuples) {
      switch (v.kind()) {
        case BASE -> {
          baseTuples.add(v);
          break;
        }
        case PROJ -> {
          HashSet<UVar> tmp = new HashSet<>();
          tmp.add(v.args()[0]);
          baseTuples.addAll(collectBaseTuple(tmp));
          break;
        }
        default -> {
          break;
        }
      }
    }
    return baseTuples;
  }

  UTerm instantiationOneSumWithTuple(UTerm body, UVar sumTuple, HashSet<UVar> freeTuples) {
    ArrayList<UTerm> terms = new ArrayList<>();
    for(UVar v : freeTuples) {
      if(v.equals(sumTuple)) {
        continue;
      }
      terms.add(body.replaceVar(sumTuple, v,false).copy());
    }
    HashSet<UVar> boundVars = new HashSet<>();
    boundVars.add(sumTuple);
    terms.add(USum.mk(boundVars, body.copy()));
    return UAdd.mk(terms);
  }

  Liastar sumsToLiaStar(
      boolean isInner,
      boolean instWithTuple,
      ArrayList<UTerm> sumList,
      ArrayList<String> sumVarList,
      HashMap<UTerm, String> termVarMap,
      HashSet<UVar> freeTuples
  ) {

    ArrayList<UTerm> newSumList = new ArrayList<>();
    copySumList(sumList, newSumList);

    UVar commonTuple = injectCommonTuple(newSumList);
    alignSummation(newSumList, commonTuple);
    boolean flag = instantiationWithPredicate(newSumList, freeTuples, termVarMap.keySet());
    mergeSameSum(newSumList);
    boolean ifInstWithTuple = false;
    if(flag == false && instWithTuple == true) {
      ifInstWithTuple = instantiationWithTuple(newSumList, commonTuple, freeTuples);
    }

    final ArrayList<UTerm> subSums = new ArrayList<>();
    final ArrayList<String> subVars = new ArrayList<>();
    replaceSumsInList(newSumList, subSums, subVars);
    Liastar constraints = null;
    ArrayList<String> innerVector = new ArrayList<>();
    HashSet<UVarTerm> isNullTuples = new HashSet<>();
    for (int i = 0; i < sumVarList.size(); ++i) {
      String innerVarName = newUliaVarName();
      innerVector.add(innerVarName);
      Liastar equation = transUexpWithoutSum(true, newSumList.get(i), termVarMap, isNullTuples);
      if(ifInstWithTuple == true) {
        equation = Liastar.mkEq(true, Liastar.mkVar(true, sumVarList.get(i)), equation);
      } else {
        equation = Liastar.mkEq(true, Liastar.mkVar(true, innerVarName), equation);
      }
      if (constraints == null) {
        constraints = equation;
      } else {
        constraints = Liastar.mkAnd(true, constraints, equation);
      }
    }
    Liastar isNullConstraints = isNullCongruence(termVarMap, isNullTuples);
    if (isNullConstraints != null)
      constraints = Liastar.mkAnd(true, constraints, isNullConstraints);
    if (!subSums.isEmpty()) {
      if(ifInstWithTuple == false) {
        freeTuples.add(commonTuple);
      }
      constraints = mkAnd(true, constraints,
          sumsToLiaStar(true, !ifInstWithTuple, subSums, subVars, termVarMap, freeTuples)
      );
    }

    if(ifInstWithTuple == true) {
      return constraints;
    } else {
      LiasumImpl result = (LiasumImpl) mkSum(isInner, sumVarList, innerVector, constraints);
      // result.updateInnerVector();
      return result;
    }
  }

  private static boolean isNullUTerm(UTerm t) {
    if (t.kind() != PRED) return false;
    UPred pred = (UPred) t;
    if (!isPredOfVarArg(pred)) return false;
    return pred.isPredKind(UPred.PredKind.FUNC) && pred.predName().equals(NAME_IS_NULL);
  }

  private static Liastar isNullCongruence(HashMap<UTerm, String> termVarMap, HashSet<UVarTerm> isNullTuples) {
    if (isNullTuples.isEmpty() || termVarMap.isEmpty()) return null;
    HashSet<UTerm> isNullUTerms = new HashSet<>(termVarMap.keySet().stream().filter(t -> isNullUTerm(t)).toList());
    HashSet<UVarTerm> existingIsNullTuples = new HashSet<>();
    for (UTerm t : isNullUTerms) {
      UPred pred = (UPred) t;
      final List<UVar> pArgs = UExprSupport.getPredVarArgs(pred);
      UVarTerm isNullTuple = UVarTerm.mk(pArgs.get(0));
      if (!isNullTuples.contains(isNullTuple))
        existingIsNullTuples.add(isNullTuple);
    }
    Liastar result = null;
    for (UVarTerm v1 : isNullTuples) {
      String var1 = termVarMap.get(v1);
      assert var1 != null;
      ArrayList<UTerm> isNullarg1 = new ArrayList<>();
      isNullarg1.add(v1);
      String isNullVar1 = termVarMap.get(UPred.mk(UPred.PredKind.FUNC, NAME_IS_NULL, isNullarg1));
      LiavarImpl liavar1 = (LiavarImpl) Liastar.mkVar(true, var1);
      LiavarImpl liaIsNullvar1 = (LiavarImpl) Liastar.mkVar(true, isNullVar1);
      for (UVarTerm v2 : existingIsNullTuples) {
        String var2 = termVarMap.get(v2);
        assert var2 != null;
        ArrayList<UTerm> isNullarg2 = new ArrayList<>();
        isNullarg2.add(v2);
        String isNullVar2 = termVarMap.get(UPred.mk(UPred.PredKind.FUNC, NAME_IS_NULL, isNullarg2));
        LiavarImpl liavar2 = (LiavarImpl) Liastar.mkVar(true, var2);
        LiavarImpl liaIsNullvar2 = (LiavarImpl) Liastar.mkVar(true, isNullVar2);
        Liastar tmp = Liastar.mkEq(true,
            liaIsNullvar1,
            Liastar.mkIte(true, Liastar.mkEq(true, liavar1, liavar2), liaIsNullvar2, liaIsNullvar1)
          );
//        Liastar tmp = Liastar.mkOr(true,
//            Liastar.mkNot(true, ),
//            Liastar.mkEq(true, liaIsNullvar1, liaIsNullvar2));
        result = (result == null) ? tmp : Liastar.mkAnd(true, result, tmp) ;
      }
    }
    return result;
  }

/*
    if(sums.size() == 1 && !(query1.equals(query2))) {
      UTerm t = sums.get(0);
      String newSumName = newUliaVarName();
      UTerm instan =  instantiateTuple((USum) t, newSumName);

      ArrayList<String> newSumVars = new ArrayList<>();
      newSumVars.add(newSumName);
      Liastar result = transUexpWithoutSum(false, instan, termMap);
      result = mkEq(false, mkVar(false, vars.get(0)), result);
      result = mkAnd(false, result, tr(false, sums, newSumVars));
      return result;
    } else {
      return tr(false, sums, vars);
    }

  }
 */

  Pair<UVar, String> getCommonTupleName(List<UTerm> sums) {
    UVar commonVar = null;
    String commonTable = null;
    for(int i = 0; i < sums.size(); ++ i) {
      USum curSum = ((USum) sums.get(i));
      for (UVar v : curSum.boundedVars()) {
        if (commonVar == null) {
          commonVar = v;
          commonTable = findTableForTuple(curSum, commonVar);
        } else {
          String vName = v.toString();
          String commonVarName = commonVar.toString();
          if( (vName.length() < commonVarName.length()) ||
              (vName.length() == commonVarName.length() && vName.compareTo(commonVarName) < 0) ) {
            commonVar = v;
            commonTable = findTableForTuple(curSum, commonVar);
          }
        }
      }
    }
    Pair<UVar, String> result = new MutablePair<>(commonVar, commonTable);
    return result;
  }

  void copySumList(List<UTerm> sums, List<UTerm> newSums) {
    for(int i = 0; i < sums.size(); ++ i) {
      newSums.add(sums.get(i).copy());
    }
  }

  String findTableForTuple(UTerm expr, UVar tuple) {
    switch (expr.kind()) {
      case ADD: case MULTIPLY: {
        for(UTerm term : expr.subTerms()) {
          String tmp = findTableForTuple(term, tuple);
          if (tmp != null) {
            return tmp;
          }
        }
        return null;
      }
      case SQUASH: {
        return findTableForTuple(((USquash)expr).body(), tuple);
      }
      case NEGATION: {
        return findTableForTuple(((UNeg)expr).body(), tuple);
      }
      case SUMMATION: {
        return findTableForTuple(((USum)expr).body(), tuple);
      }
      case TABLE: {
        UTable tmp = (UTable) expr;
        if (tmp.var().equals(tuple)) {
          return tmp.tableName().toString();
        } else {
          return null;
        }
      }
      default: {
        return null;
      }
    }
  }

  UTerm replaceTagetTupleFromOneSum(
      USum cur,
      UVar v,
      UVar commonTupleNewName,
      ArrayList<UVar> preVars) {

    cur.boundedVars().remove(v);
    cur.replaceVarInplace(v, commonTupleNewName, true);
    if (cur.boundedVars().isEmpty()) {
      preVars.add(v);
      return cur.body().copy();
    } else {
      preVars.add(v);
      return cur.copy();
    }
  }

  UTerm injectTupleForOneUTerm(
      USum cur,
      UVar commonTuple,
      UVar commonTupleNewName,
      ArrayList<UVar> preVars,
      ArrayList<String> selectedVarTables,
      ArrayList<UTerm> preSums
  ) {

    Set<UVar> boundTuples = cur.boundedVars();
    if (boundTuples.contains(commonTuple)) {
      return replaceTagetTupleFromOneSum(cur, commonTuple, commonTupleNewName, preVars);
    }

    for(UVar v : boundTuples) {
      if(preVars.contains(v)) {
        return replaceTagetTupleFromOneSum(cur, v, commonTupleNewName, preVars);
      }
    }

    for (String commonTable : selectedVarTables) {
      HashSet<UVar> candidateVars = new HashSet<>();
      for (UVar v : boundTuples) {
        String tableName = findTableForTuple(cur.body(), v);
        if (tableName == null) {
          continue;
        }
        if (tableName.equals(commonTable)) {
          candidateVars.add(v);
        }
      }

      UVar v = null;
      int maxScore = 0;
      for(UVar tmp : candidateVars) {
        USum curCopy = (USum) cur.copy();
        UTerm expAfterInject = replaceTagetTupleFromOneSum(curCopy, tmp, commonTupleNewName, new ArrayList<>());
        int score = computeScoreForInjectTuple(preSums, expAfterInject);

        if(v == null) {
          v = tmp;
          maxScore = score;
        } else {
          if(score > maxScore) {
            v = tmp;
            maxScore = score;
          }
        }
      }

      if(v != null) {
        return replaceTagetTupleFromOneSum(cur, v, commonTupleNewName, preVars);
      }
    }

    UVar v = null;
    int maxScore = 0;
    for(UVar tmp : boundTuples) {
      if(v == null) {
        v = tmp;
      } else {
        USum curCopy = (USum) cur.copy();
        UTerm expAfterInject = replaceTagetTupleFromOneSum(curCopy, v, commonTupleNewName, new ArrayList<>());
        int score = computeScoreForInjectTuple(preSums, expAfterInject);
        if(score > maxScore)
          v = tmp;
      }
    }
    selectedVarTables.add( findTableForTuple(cur.body(), v));
    return replaceTagetTupleFromOneSum(cur, v, commonTupleNewName, preVars);
  }

  int computeScoreForInjectTuple(List<UTerm> sums, UTerm exp) {
    int score = 0;
    List<UTerm> thisTerms = null;
    if(exp instanceof USum)
      thisTerms = ((USum)exp).body().subTerms();
    else if(exp instanceof UMul)
      thisTerms = ((UMul)exp).subTerms();
    else
      return 0;

    for(int i = 0; i < sums.size(); ++ i) {

      List<UTerm> thatTerms = null;
      UTerm thatExp = sums.get(i);
      if(thatExp instanceof USum)
        thatTerms = ((USum)thatExp).body().subTerms();
      else if(thatExp instanceof UMul)
        thatTerms = ((UMul)thatExp).subTerms();
      else
        thatTerms = new ArrayList<>();

      for(UTerm t : thatTerms) {
        score = thisTerms.contains(t) ? (score + 1) : score;
      }
    }

    return score;
  }

  UVar injectCommonTuple(List<UTerm> sums) {
    if (sums.isEmpty()) return null;

    Pair<UVar, String> tmp = getCommonTupleName(sums);
    UVar commonTuple = tmp.getLeft();
    String commonTable = tmp.getRight();
    UVar commonTupleNewName = UVar.mkBase(UName.mk(newUliaVarName()));

    ArrayList<UVar> selectedVars = new ArrayList<>();
    ArrayList<String> selectedVarTables = new ArrayList<>();
    selectedVarTables.add(commonTable);
    for (int i = 0; i < sums.size(); ++i) {
      USum cur = (USum) sums.get(i);
      ArrayList<UTerm> preSums = new ArrayList<>();
      for(int j = 0; j < i; ++ j)
        preSums.add(sums.get(j));

      sums.set(i, injectTupleForOneUTerm(cur, commonTuple, commonTupleNewName, selectedVars, selectedVarTables, preSums));
    }

    return commonTupleNewName;
  }

  UVar dedupProjInVar(UVar v, boolean innerProj) {
    switch (v.kind()) {
      case BASE -> {
        return v;
      }
      case PROJ -> {
        if (innerProj) {
          return UVar.mkBase(dedupProjInVar(v.args()[0], true).name());
        } else {
          return UVar.mkProj(v.name(), dedupProjInVar(v.args()[0], true));
        }
      }
      case CONCAT -> {
        return UVar.mkConcat(
            dedupProjInVar(v.args()[0], false), dedupProjInVar(v.args()[1], false));
      }
      default -> {
        assert false;
        return v;
      }
    }
  }

  UTerm dedupProject(UTerm u) {
    switch (u.kind()) {
      case ADD, MULTIPLY, NEGATION, SQUASH, PRED: {
        final List<UTerm> tmp = new ArrayList<>();
        for (UTerm t : u.subTerms()) {
          tmp.add(dedupProject(t));
        }
        switch (u.kind()) {
          case ADD: return UAdd.mk(tmp);
          case MULTIPLY: return UMul.mk(tmp);
          case NEGATION: return UNeg.mk(tmp.get(0));
          case SQUASH: return USquash.mk(tmp.get(0));
          case PRED: return UPred.mk(((UPred) u).predKind(), ((UPred) u).predName(), tmp);
        }
      }
      case TABLE, VAR: {
        final UVar v = dedupProjInVar(((UAtom) u).var(), false);
        return u.kind() == TABLE ? UTable.mk(((UTable) u).tableName(), v) : UVarTerm.mk(v);
      }
      default:
        return u;
    }
  }

  void simplifyProject(List<UTerm> sums) {
    for (int i = 0; i < sums.size(); i++) {
      UTerm u = sums.get(i);
      sums.set(i, dedupProject(u));
    }
  }

  static HashSet<Pair<UVar, UVar>> intersectEqRel(HashSet<Pair<UVar, UVar>> s1, HashSet<Pair<UVar, UVar>> s2) {
    HashSet<Pair<UVar, UVar>> result = new HashSet<>();
    for(Pair<UVar, UVar> pair : s1) {
      UVar left = pair.getLeft();
      UVar right = pair.getRight();
      if (s2.contains(pair) || s2.contains(Pair.of(right, left))) {
        result.add(Pair.of(left.copy(), right.copy()));
      }
    }
    return result;
  }

  static HashSet<Pair<UVar, UVar>> collectPredicatesFromOneTerm(UTerm curExp) {
    HashSet<Pair<UVar, UVar>> eqVars = new HashSet<>();
    if(curExp instanceof USquash) {
      curExp = ((USquash) curExp).body();
    }
    if (curExp instanceof UMul) {
      List<UTerm> subts = curExp.subTerms();
      for (UTerm t : subts) {
        if (t instanceof UPred) {
          final UPred pred = (UPred) t;
          if (pred.isPredKind(UPred.PredKind.EQ) && isPredOfVarArg(pred)) {
            final List<UVar> pArgs = UExprSupport.getPredVarArgs(pred);
            assert pArgs.size() == 2;
            eqVars.add(Pair.of(pArgs.get(0).copy(), pArgs.get(1).copy()));
          }
        } else if (t instanceof USquash) {
          HashSet<Pair<UVar, UVar>> tmp = collectPredicatesFromOneTerm(t);
          eqVars.addAll(tmp);
        }
      }
    } else if(curExp instanceof UAdd) {
      List<UTerm> subts = curExp.subTerms();
      HashSet<Pair<UVar, UVar>> eqRel = null;
      for (UTerm t : subts) {
        HashSet<Pair<UVar, UVar>> tmp = collectPredicatesFromOneTerm(t);
        if(eqRel == null) {
          eqRel = tmp;
        } else {
          eqRel = intersectEqRel(eqRel, tmp);
        }
      }
      return eqRel;
    }
    return eqVars;
  }

  static Set<Pair<UVar, UVar>> collectCommonPredicates(ArrayList<Set<Pair<UVar, UVar>>> allEqVars) {
    Set<Pair<UVar, UVar>> result = new HashSet<>();
    for (int i = 0; i < allEqVars.size(); ++i) {
      Set<Pair<UVar, UVar>> curEqs = allEqVars.get(i);
      for (int j = 0; j < allEqVars.size(); ++j) {
        if(j == i) {
          continue;
        }
        Set<Pair<UVar, UVar>> thatEqs = allEqVars.get(j);
        Set<Pair<UVar, UVar>> tmp = new HashSet<>(curEqs);
        for (Pair<UVar, UVar> pair : tmp) {
          UVar v1 = pair.getLeft();
          UVar v2 = pair.getRight();
          Pair<UVar, UVar> anotherPair = Pair.of(v2, v1);
          if (!thatEqs.contains(pair) && !thatEqs.contains(anotherPair)) {
            curEqs.remove(pair);
          }
        }
      }
      result.addAll(curEqs);
    }
    return result;
  }

  static HashSet<UVar> mergeSets(HashSet<UVar> set1, HashSet<UVar> set2) {
    HashSet<UVar> result = new HashSet<>();
    for(UVar v : set1) {
      if(set2.contains(v)) {
        result.add(v);
      }
    }
    return result;
  }

  static ArrayList<HashSet<UVar>> mergeEqRels(ArrayList<HashSet<UVar>> rel1, ArrayList<HashSet<UVar>> rel2) {
    if(rel1.size() > rel2.size()) {
      return mergeEqRels(rel2, rel1);
    }
    ArrayList<HashSet<UVar>> result = new ArrayList<>();
    for(HashSet<UVar> thisSet : rel1) {
      HashSet<UVar> target = null;
      for(HashSet<UVar> thatSet : rel2) {
        HashSet<UVar> tmp = mergeSets(thisSet, thatSet);
        if(tmp.size() > 1) {
          target = thatSet;
          result.add(tmp);
          break;
        }
      }
      if(target != null) {
        rel2.remove(target);
      }
    }

    return result;
  }


  static ArrayList<HashSet<UVar>> analyseEqRels(ArrayList<Set<Pair<UVar, UVar>>> allEqVars) {
    if(allEqVars.isEmpty()) {
      return new ArrayList<>();
    }
    ArrayList<HashSet<UVar>> result = buildEqRelation(allEqVars.get(0));
    for(int i = 1; i < allEqVars.size(); ++ i) {
      ArrayList<HashSet<UVar>> tmp = buildEqRelation(allEqVars.get(i));
      result = mergeEqRels(result, tmp);
    }
    return result;
  }


  static ArrayList<HashSet<UVar>> collectPredicates(List<UTerm> sums) {
    ArrayList<Set<Pair<UVar, UVar>>> allEqVars = new ArrayList<>();
    for (int i = 0; i < sums.size(); ++i) {
      UTerm curExp = sums.get(i);
      Set<Pair<UVar, UVar>> eqVars = collectPredicatesFromOneTerm(curExp);
      allEqVars.add(eqVars);
    }
    return analyseEqRels(allEqVars);
  }


//  boolean replaceEqualTuples(List<UTerm> sums) {
//    Set<Pair<UVar, UVar>> eqVarPairs = collectPredicates(sums);
//    if(eqVarPairs.isEmpty()) {
//      return false;
//    }
//    for (int i = 0; i < sums.size(); ++i) {
//      UTerm cur = sums.get(i);
//      for (Pair<UVar, UVar> v : eqVarPairs) {
//        cur.replaceVarInplace(v.getLeft(), v.getRight(), false);
//      }
//    }
//    simplifyProject(sums);
//    return true;
//  }

  void replaceSumsInList(List<UTerm> sums, List<UTerm> subSums, List<String> subVars) {
    HashMap<USum, String> sumMap = new HashMap<>();
    for (int i = 0; i < sums.size(); ++i) {
      sums.set(i, replaceSummations(sumMap, sums.get(i)));
    }
    subSums.addAll(sumMap.keySet());
    for (int i = 0; i < subSums.size(); ++i) {
      subVars.add(sumMap.get(subSums.get(i)).toString());
    }
  }

  UTerm replaceSummations(HashMap<USum, String> sumMap, UTerm uexp) {
    switch (uexp.kind()) {
      case SUMMATION:
        for (UTerm t : sumMap.keySet()) {
          if (t.equals(uexp)) return ULiaVar.mk(sumMap.get(t));
        }
        final String sumName = newUliaVarName();
        final ULiaVar newVar = ULiaVar.mk(sumName);
        sumMap.put((USum) uexp, sumName);
        return newVar;
      case MULTIPLY, ADD, PRED, FUNC: {
        final List<UTerm> subTerms = uexp.subTerms();
        final List<UTerm> newSubTerms = new ArrayList<>();
        for (UTerm t : subTerms) {
          newSubTerms.add(replaceSummations(sumMap, t));
        }
        return switch (uexp.kind()) {
          case MULTIPLY -> UMul.mk(newSubTerms);
          case ADD -> UAdd.mk(newSubTerms);
          case FUNC -> UFunc.mk(((UFunc)uexp).funcKind(), ((UFunc)uexp).funcName(), newSubTerms);
          default -> UPred.mk(((UPred) uexp).predKind(), ((UPred) uexp).predName(), newSubTerms);
        };
      }
      case NEGATION:
        return UNeg.mk(replaceSummations(sumMap, ((UNeg) uexp).body()));
      case SQUASH:
        return USquash.mk(replaceSummations(sumMap, ((USquash) uexp).body()));
      default:
        return uexp;
    }
  }

  void alignSummation(List<UTerm> sums, UVar commonTuple) {
    if(sums.size() <= 1)
      return;

    for(int i = 0; i < sums.size(); ++ i) {
      UTerm term = sums.get(i);
      if(term instanceof UMul && term.subTerms().size() == 1) {
        sums.set(i, term.subTerms().get(0));
      }
    }

    boolean hasSquashSum = false;
    boolean hasNoSquashSum = false;
    for(UTerm t : sums) {
      if(t instanceof USquash && ((USquash) t).body() instanceof USum) {
        hasSquashSum = true;
      }
      else if (t instanceof USquash && !(((USquash) t).body() instanceof USum)) {
        hasNoSquashSum = true;
      }
    }

    if(hasSquashSum && hasNoSquashSum) {
      for (int i = 0; i < sums.size(); ++i) {
        UTerm term = sums.get(i);
        if(term instanceof USquash && ((USquash) term).body() instanceof USum) {
          UTerm alignedTerm = splitSummation(((USquash) term).body());
          if(alignedTerm instanceof UMul) {
            for (int j = 0; j < alignedTerm.subTerms().size(); ++ j) {
              UTerm t = alignedTerm.subTerms().get(j);
              if(t instanceof USum && ((USum) t).boundedVars().size() == 1) {
                USum tmp = (USum)t;
                UVar bVar = new ArrayList<>(tmp.boundedVars()).get(0);
                UTerm body = tmp.body();
                alignedTerm.subTerms().set(j, UAdd.mk(tmp.copy(), body.replaceVar(bVar, commonTuple,false)));
                break;
              }
            }
          }
          sums.set(i, USquash.mk(alignedTerm));
        }
      }
    }
  }

  /** \sum{t0,t1}(E * f(t0) * g(t1)) -> E * \sum{t0}(f(t0) * \sum{t1}g(t1)) * */
  UTerm splitSummation(UTerm expr) {
    expr = transformSubTerms(expr, this::splitSummation);
    // Skip if not a summation, or the summation has already been split
    if (expr.kind() != SUMMATION) return expr;
    final USum summation = (USum) expr;
    if (summation.body().kind() != MULTIPLY) return expr;
    if (summation.boundedVars().size() == 1) {
      final UVar boundedVar = summation.boundedVars().iterator().next();
      if (all(summation.body().subTerms(), t -> t.kind() == SUMMATION || t.isUsing(boundedVar)))
        return expr;
    }

    // Register each sub-term, check which bounded var's summation it belongs to
    final List<UTerm> constTerm = new ArrayList<>();
    final List<UVar> boundedVarList =
        summation.boundedVars().stream().sorted(UVar::baseVarComparator).toList();
    final Map<UVar, List<UTerm>> termsMap = new HashMap<>();
    boundedVarList.forEach(v -> termsMap.put(v, new ArrayList<>()));
    for (UTerm subTerm : summation.body().subTerms()) {
      boolean isConst = true;
      for (int bound = boundedVarList.size(), i = bound - 1; i >= 0; --i) {
        final UVar boundedVar = boundedVarList.get(i);
        if (subTerm.isUsing(boundedVar)) {
          termsMap.get(boundedVar).add(subTerm);
          isConst = false;
          break;
        }
      }
      if (isConst) constTerm.add(subTerm);
    }
    // Construct splitted summation: \sum{..}(E0 * \sum{..}(E1 * ..))
    UTerm curSum = null;
    for (int bound = boundedVarList.size(), i = bound - 1; i >= 0; --i) {
      final UVar boundedVar = boundedVarList.get(i);
      final List<UTerm> curSubTerms = new ArrayList<>(termsMap.get(boundedVar));
      if (curSum != null) curSubTerms.add(curSum);
      final Set<UVar> varSet = new HashSet<>(Collections.singleton(boundedVar));
      curSum = USum.mk(varSet, UMul.mk(curSubTerms));
    }
    // Add const terms if exists: E * \sum{..}(E * ..)
    if (!constTerm.isEmpty()) {
      final UTerm mul = UMul.mk(constTerm);
      mul.subTerms().add(curSum);
      return mul;
    } else return curSum;
  }

/*
  Liastar tr(boolean isInnerStar,
             List<UTerm> sums,
             List<String> liaVars,
             HashMap<UTerm, String> termVarMap
             // NaturalCongruence<UVar> prevEqRelation, /* outer layer eq relations e.g. `t = t1` for \sum{t2}
             // Set<UVar> prevBaseVars, /* [t, t1, t2, ...]
             // Set<UVar> prevExposedVars /* [t, a(t), t1, a1(t1), a1'(t1), t2, ...]
  ) {
    injectCommonTuple(sums);
    alignSummation(sums);
    // final UVar injectBoundedVar = injectCommonTuple(sums);
    // assert injectBoundedVar != null;
    if (sums.size() > 1) {
      boolean flag = replaceEqualTuples(sums);
      for (int i = 0; i < sums.size(); i++) {
        for (int j = i + 1; j < sums.size(); j++) {
          if (sums.get(i).equals(sums.get(j))) {
            sums.set(j, sums.get(i));
          }
        }
      }
    }

    final ArrayList<UTerm> subSums = new ArrayList<>();
    final ArrayList<String> subVars = new ArrayList<>();
    replaceSums(sums, subSums, subVars);

    // Get vars for this recursion
    // final Set<UVar> newBaseVars = new HashSet<>(prevBaseVars);
    // newBaseVars.add(injectBoundedVar);
    // final Set<UVar> newExposedVars = new HashSet<>(prevExposedVars);
    // sums.forEach(s -> newExposedVars.addAll(searchFreeUnaryVars(((USum) s).body())));
    // final Set<NaturalCongruence<UVar>> enumEqRelations = getEnumeratedEqRelations(newExposedVars, prevEqRelation);
    // assert !enumEqRelations.isEmpty();

    Liastar constraints = null;
    ArrayList<String> innerVector = new ArrayList<>();
    HashMap<UTerm, String> termToVar = new HashMap<>();
    for (int i = 0; i < liaVars.size(); ++i) {
      String innerVarName = newUliaVarName();
      innerVector.add(innerVarName);
      Liastar equation = transUexpWithoutSum(true, sums.get(i), termToVar);
      equation = Liastar.mkEq(true, Liastar.mkVar(true, innerVarName), equation);
      if (constraints == null) constraints = equation;
      else constraints = Liastar.mkAnd(true, constraints, equation);
    }
    if (!subSums.isEmpty())
      constraints = mkAnd(true, constraints, tr(true, subSums, subVars));
    LiasumImpl result = (LiasumImpl) mkSum(isInnerStar, (ArrayList<String>) liaVars, innerVector, constraints);
    result.updateInnerVector();

    // Liastar result = null;
    // for (NaturalCongruence<UVar> eqRelation : enumEqRelations) {
    //   // TODO: translate eq relations of tuples to constraints on sum
    //   Liastar constraints = null;
    //   ArrayList<String> innerVector = new ArrayList<>();
    //   HashMap<UTerm, String> termToVar = new HashMap<>();
    //   for (int i = 0; i < liaVars.size(); ++i) {
    //     String innerVarName = newUliaVarName();
    //     innerVector.add(innerVarName);
    //     Liastar equation = transUexpWOSum(true, sums.get(i), termToVar);
    //     equation = Liastar.mkEq(true, Liastar.mkVar(true, innerVarName), equation);
    //     if (constraints == null) constraints = equation;
    //     else constraints = Liastar.mkAnd(true, constraints, equation);
    //   }
    //   if (!subSums.isEmpty()) {
    //     final Liastar trLia = tr(true, subSums, subVars, eqRelation, newBaseVars, newExposedVars);
    //     constraints = mkAnd(true, constraints, trLia);
    //   }
    //   LiasumImpl sum = (LiasumImpl) mkSum(isInnerStar, (ArrayList<String>) liaVars, innerVector, constraints);
    //   sum.updateInnerVector();
    //   result = result == null ? sum : mkPlus(isInnerStar, result, sum);
    // }
    return result;
  }
  */

  private Set<UVar> searchFreeUnaryVars(UTerm expr) {
    if (expr.kind() == UKind.SUMMATION) return Collections.emptySet();

    final Set<UVar> freeUnaryVars = new HashSet<>();
    if (expr.kind().isTermAtomic()) {
      final Set<UVar> unaryVars = new HashSet<>();
      switch (expr.kind()) {
        case TABLE, VAR -> unaryVars.addAll(UVar.getUnaryVars(((UAtom) expr).var()));
        case PRED -> {
          final List<UTerm> args = ((UPred) expr).args();
          for (UTerm arg : args) {
            if (arg.kind().isVarTerm())
              unaryVars.addAll(UVar.getUnaryVars(((UVarTerm) arg).var()));
          }
        }
      }
      for (UVar var : unaryVars) {
        //if (any(freeBaseVars, var::isUsing)) freeUnaryVars.add(var);
        freeUnaryVars.add(var.copy());
      }
    } else expr.subTerms().forEach(t -> freeUnaryVars.addAll(searchFreeUnaryVars(t)));

    return freeUnaryVars;
  }

  private Set<NaturalCongruence<UVar>> getEnumeratedEqRelations(Set<UVar> exposedVars,
                                                                 NaturalCongruence<UVar> prevEqRelation) {
    if (prevEqRelation == null) prevEqRelation = NaturalCongruence.mk();

    final Set<UVar> prevExposedVars = prevEqRelation.keys();
    Set<NaturalCongruence<UVar>> prevEnumRelations = new HashSet<>(Collections.singleton(prevEqRelation));
    Set<NaturalCongruence<UVar>> curEnumRelations = new HashSet<>();
    for (UVar var : filter(exposedVars, v -> !prevExposedVars.contains(v))) {
      for (NaturalCongruence<UVar> relation : prevEnumRelations) {
        final Set<UVar> prevVars = new HashSet<>(relation.keys());
        while (!prevVars.isEmpty()) {
          final UVar chosenVar = prevVars.iterator().next();
          final NaturalCongruence<UVar> eqRelationCopy = (NaturalCongruence<UVar>) relation.copy();
          eqRelationCopy.putCongruent(var, chosenVar);
          curEnumRelations.add(eqRelationCopy);
          prevVars.removeAll(relation.eqClassOf(chosenVar));
        }
        // Also put itself into a singleton class
        final NaturalCongruence<UVar> eqRelationCopy = (NaturalCongruence<UVar>) relation.copy();
        eqRelationCopy.putCongruent(var, var);
        curEnumRelations.add(eqRelationCopy);
      }
      prevEnumRelations = curEnumRelations;
      curEnumRelations = new HashSet<>();
    }
    return prevEnumRelations;
  }

  // summations in exp have been replaced by new variables
  // Then transUexpWithoutSum translates exp into LIA formula
  // uTermToLiaVar is used to replace the same terms with same variables
  Liastar transUexpWithoutSum(boolean innerStar, UTerm exp, Map<UTerm, String> uTermToLiaVar, HashSet<UVarTerm> isnullTuples) {
    switch (exp.kind()) {
      case SUMMATION -> throw new UnsupportedOperationException("should not have summation when transforming to Lia!");
      case ADD -> {
        Liastar result = null;
        final List<UTerm> subTerms = exp.subTerms();
        for (UTerm t : subTerms) {
          Liastar curLia = transUexpWithoutSum(innerStar, t, uTermToLiaVar, isnullTuples);
          curLia = curLia.simplifyIte();
          if(result == null) {
            result = curLia;
          } else if(result instanceof LiaiteImpl) {
            result = ((LiaiteImpl)result).plusIte(curLia);
          } else if(curLia instanceof LiaiteImpl) {
            result = ((LiaiteImpl)curLia).plusIte(result);
          } else {
            result = Liastar.mkPlus(innerStar, result, curLia);
          }
        }
        return result;
      }
      case MULTIPLY -> {
        Liastar result = null;
        final List<UTerm> subTerms = exp.subTerms();
        Liastar iteNonzeroCond = null;
        for (UTerm t : subTerms) {
          Liastar curLia = transUexpWithoutSum(innerStar, t, uTermToLiaVar, isnullTuples);
          Liastar[] condOpArray = new Liastar[2];
          boolean hasZeroIte = ishasZeroIte(innerStar, curLia, condOpArray);
          if(hasZeroIte) {
            Liastar cond = condOpArray[0];
            Liastar op = condOpArray[1];
            iteNonzeroCond = (iteNonzeroCond == null) ? cond : mkAnd(innerStar, iteNonzeroCond, cond);
          } else {
            if (result == null) result = curLia;
            else {
              if (result instanceof LiaiteImpl) result = ((LiaiteImpl) result).MultIte(curLia);
              else if (curLia instanceof LiaiteImpl) result = ((LiaiteImpl) curLia).MultIte(result);
              else result = Liastar.mkMult(innerStar, result, curLia);
            }
          }
        }
        if(iteNonzeroCond != null) {
          if(result == null) {
            result = mkConst(innerStar, 1);
          }
          result = mkIte(innerStar, iteNonzeroCond, result, mkConst(innerStar, 0));
        }
        return result;
      }
      case NEGATION, SQUASH -> {
        final UTerm body = ((UUnary) exp).body();
        final Liastar cond =
            Liastar.mkEq(
                innerStar,
                transUexpWithoutSum(innerStar, body, uTermToLiaVar, isnullTuples),
                Liastar.mkConst(innerStar, 0));
        return exp.kind() == NEGATION
            ? Liastar.mkIte(innerStar, cond, Liastar.mkConst(innerStar, 1), Liastar.mkConst(innerStar, 0))
            : Liastar.mkIte(innerStar, cond, Liastar.mkConst(innerStar, 0), Liastar.mkConst(innerStar, 1));
      }
      case CONST -> {
        return Liastar.mkConst(false, ((UConst) exp).value());
      }
      case TABLE -> {
        final String varName = uTermToLiaVar.computeIfAbsent((UTable) exp, t -> newUliaVarName());
        return Liastar.mkVar(innerStar, varName);
      }
      case PRED -> {
        // Case 1. ULiaVar
        if (exp instanceof ULiaVar) return Liastar.mkVar(innerStar, exp.toString());
        final UPred pred = (UPred) exp;
        if (pred.isPredKind(UPred.PredKind.FUNC) && isPredOfVarArg(pred)) {
          // Case 2. [p(a(t))]. View `p(a(t))` as a variable
          final List<UVar> pArgs = UExprSupport.getPredVarArgs(pred);
          assert pArgs.size() == 1;
          uTermToLiaVar.computeIfAbsent(UVarTerm.mk(pArgs.get(0)), v -> newUliaVarName());
          final String varName = uTermToLiaVar.computeIfAbsent(pred, v -> newUliaVarName());
          final Liastar liaVar = Liastar.mkVar(innerStar, varName);
          if (pred.predName().equals(NAME_IS_NULL))
            isnullTuples.add(UVarTerm.mk(pArgs.get(0)));
          return Liastar.mkIte(
              innerStar,
              Liastar.mkEq(innerStar, liaVar, Liastar.mkConst(innerStar, 0)),
              Liastar.mkConst(innerStar, 0),
              Liastar.mkConst(innerStar, 1));
        } else if (pred.isBinaryPred()) {
          // Case 3. [U-expr0 <binary op> U-expr1]
          final Liastar liaVar0 = transUexpWithoutSum(innerStar, pred.args().get(0), uTermToLiaVar, isnullTuples);
          final Liastar liaVar1 = transUexpWithoutSum(innerStar, pred.args().get(1), uTermToLiaVar, isnullTuples);
          final Liastar target = switch (pred.predKind()) {
            case EQ -> Liastar.mkEq(innerStar, liaVar0, liaVar1);
            case NEQ -> Liastar.mkNot(innerStar, Liastar.mkEq(innerStar, liaVar0, liaVar1));
            case LE -> Liastar.mkLe(innerStar, liaVar0, liaVar1);
            case LT -> Liastar.mkLt(innerStar, liaVar0, liaVar1);
            case GE -> Liastar.mkLe(innerStar, liaVar1, liaVar0);
            case GT -> Liastar.mkLt(innerStar, liaVar1, liaVar0);
            default -> throw new IllegalArgumentException("unsupported predicate in Uexpr.");
          };
          return Liastar.mkIte(innerStar, target, Liastar.mkConst(innerStar, 1), Liastar.mkConst(innerStar, 0));
        } else {
          throw new UnsupportedOperationException("unsupported UPred var type.");
        }
      }
      case VAR, STRING -> {
        final String varName = uTermToLiaVar.computeIfAbsent(exp, v -> newUliaVarName());
        return Liastar.mkVar(innerStar, varName);
      }
      case FUNC -> {
        UFunc func = (UFunc) exp;
        String funcName = func.funcName().toString();
        switch (funcName) {
          case "divide": {
            Liastar result = null;
            final List<UTerm> subTerms = exp.subTerms();
            for (UTerm t : subTerms) {
              Liastar curLia = transUexpWithoutSum(innerStar, t, uTermToLiaVar, isnullTuples);
              if(result == null) {
                result = curLia;
              } else {
                result = Liastar.mkDiv(innerStar, result, curLia);
              }
            }
            return result;
          }
          case "sqrt": {
            assert exp.subTerms().size() == 1;
            UTerm operand = exp.subTerms().get(0);
            Liastar liaOp = transUexpWithoutSum(innerStar, operand, uTermToLiaVar, isnullTuples);
            return Liastar.mkFunc(innerStar, "sqrt", liaOp);
          }
          case "minus": {
            assert exp.subTerms().size() == 2;
            UTerm op0 = exp.subTerms().get(0);
            UTerm op1 = exp.subTerms().get(1);
            Liastar liaOp0 = transUexpWithoutSum(innerStar, op0, uTermToLiaVar, isnullTuples);
            Liastar liaOp1 = transUexpWithoutSum(innerStar, op1, uTermToLiaVar, isnullTuples);
            return Liastar.mkFunc(innerStar, "minus", List.of(liaOp0, liaOp1));
          }
          case "`upper`", "upper": {
            assert exp.subTerms().size() == 1;
            UTerm operand = exp.subTerms().get(0);
            Liastar liaOp = transUexpWithoutSum(innerStar, operand, uTermToLiaVar, isnullTuples);
            return Liastar.mkFunc(innerStar, "upper", liaOp);
          }
          case "`lower`", "lower": {
            assert exp.subTerms().size() == 1;
            UTerm operand = exp.subTerms().get(0);
            Liastar liaOp = transUexpWithoutSum(innerStar, operand, uTermToLiaVar, isnullTuples);
            return Liastar.mkFunc(innerStar, "lower", liaOp);
          }
          default: {
            throw new UnsupportedOperationException("unsupported function: " + funcName);
          }
        }
      }
      default -> throw new UnsupportedOperationException("unsupported UTerm type.");
    }
  }
}

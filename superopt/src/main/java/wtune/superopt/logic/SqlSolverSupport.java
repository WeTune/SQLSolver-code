package wtune.superopt.logic;

import org.apache.commons.lang3.tuple.Pair;
import wtune.common.utils.NameSequence;
import wtune.common.utils.NaturalCongruence;
import wtune.superopt.liastar.*;
import wtune.superopt.uexpr.*;

import java.util.*;
import java.util.stream.Collectors;

import static wtune.common.utils.IterableSupport.all;
import static wtune.common.utils.IterableSupport.any;
import static wtune.common.utils.SetSupport.filter;
import static wtune.superopt.liastar.LiaStar.*;
import static wtune.superopt.uexpr.UExprSupport.*;
import static wtune.superopt.uexpr.UKind.*;
import static wtune.superopt.uexpr.UName.NAME_IS_NULL;
import static wtune.superopt.uexpr.PredefinedFunctions.*;

public class SqlSolverSupport {

  private final UTerm query1;
  private final UTerm query2;
  private final UVar outVar;
  private final NameSequence liaVarName;
  private final BoundVarMatcher matcher;

  public SqlSolverSupport(UTerm q1, UTerm q2, UVar v) {
    this.query1 = q1;
    this.query2 = q2;
    this.outVar = v;
    liaVarName = NameSequence.mkIndexed("u", 0);
    matcher = new BoundVarMatcher(liaVarName, outVar);
  }

  public LiaStar uexpToLiastar() {
    Map<USum, String> sumVarMap = new HashMap<>();
    Set<USum> sums1 = new HashSet<>(), sums2 = new HashSet<>();
    UTerm q1Lia = replaceSummations(sumVarMap, sums1, query1);
    UTerm q2Lia = replaceSummations(sumVarMap, sums2, query2);

    LiaStar result;
    if (sumVarMap.isEmpty()) { // no summation
      result = uexpWOSumToLiastar(q1Lia, q2Lia);
    } else {
      result = uexpWithSumToLiastar(q1Lia, q2Lia, sumVarMap, sums1, sums2);
    }
    // simplify the LIA* formula
    return LiaStarSimplifier.getInstance().simplify(result);
  }

  HashSet<UVar> initFreeTuples() {
    HashSet<UVar> result = new HashSet<>();
    if (outVar.kind() == UVar.VarKind.BASE) {
      result.add(outVar.copy());
    } else {
      result.addAll(List.of(outVar.args()));
    }
    return result;
  }

  LiaStar uexpWithSumToLiastar(UTerm t1, UTerm t2, Map<USum, String> sumVarMap,
                               Set<USum> sumSet1, Set<USum> sumSet2) {
    HashMap<UTerm, String> termMap = new HashMap<>();
    LiaStar result = LiaStar.mkNot(false,
        LiaStar.mkEq(false,
            transUexpWithoutSum(false, t1, termMap, new HashSet<>()),
            transUexpWithoutSum(false, t2, termMap, new HashSet<>())
        )
    );

    // convert the map "sumVarMap" to two lists "sums" and "sumVars"
    // For each i, (sums[i] -> sumVars[i]) represents an entry in "sumVarMap"
    ArrayList<UTerm> sums = new ArrayList<>();
    ArrayList<String> sumVars = new ArrayList<>();
    for (Map.Entry<USum, String> entry : sumVarMap.entrySet()) {
      sums.add(entry.getKey());
      sumVars.add(entry.getValue());
    }

    // For each summation S in the set, find i so that S equals sums[i]
    // Each such index refers to a map entry (especially the key)
    Set<Integer> sumIndexSet1 = sumSet1.stream().map(sums::indexOf).collect(Collectors.toSet());
    Set<Integer> sumIndexSet2 = sumSet2.stream().map(sums::indexOf).collect(Collectors.toSet());

    HashSet<UVar> freeTuples = initFreeTuples();
    result = LiaStar.mkAnd(false, result,
        sumsToLiaStar(false, true, sums, sumVars, sumIndexSet1, sumIndexSet2, termMap, freeTuples)
    );
    result.prepareInnervector(new HashSet<>(result.collectVarSet()));
    if (LogicSupport.dumpLiaFormulas) {
      System.out.println("Lia* before simplification: ");
      System.out.println(result);
    }
    return result;
  }

  private LiaStar getOrRegisterLiaForUVar(UVar uVar, Map<UVar, String> uVarsToLiaVars) {
    assert uVar.isUnaryVar();
    LiaStar baseLia = null;
    final UVar baseVar = UVar.getSingleBaseVar(uVar);
    for (UVar v : uVarsToLiaVars.keySet()) {
      if (baseVar.equals(v)) {
        final String varName = uVarsToLiaVars.get(v);
        baseLia = LiaStar.mkVar(false, varName);
        break;
      }
    }
    if (baseLia == null) {
      final String varName = newUliaVarName();
      uVarsToLiaVars.put(baseVar, varName);
      baseLia = LiaStar.mkVar(false, varName);
    }
    return uVar.is(UVar.VarKind.BASE) ?
        baseLia : LiaStar.mkFunc(false, uVar.name().toString(), baseLia);
  }

  LiaStar transUexpNoSum(UTerm exp, Map<UVar, String> uVarsToLiaVars) {
    switch (exp.kind()) {
      case SUMMATION -> {
        // should not have summation!"
        assert false;
        return null;
      }
      case ADD -> {
        LiaStar result = null;
        final List<UTerm> subt = exp.subTerms();

        int constVal = 0;
        int i = 0;
        for (i = 0; i < subt.size(); ++ i) {
          UTerm cur = subt.get(i);
          if (cur instanceof UConst)
            constVal = constVal + ((UConst)cur).value();
          else
            break;
        }
        if (i == subt.size()) return mkConst(false, constVal);

        for (UTerm t : subt) {
          final LiaStar curLia = transUexpNoSum(t, uVarsToLiaVars);
          if (curLia instanceof LiaConstImpl) {
            if ( ((LiaConstImpl)curLia).getValue() == 0 )
              continue;
          }
          if (result == null) {
            result = curLia;
          } else {
            if (result instanceof LiaIteImpl) result = ((LiaIteImpl) result).plusIte(curLia);
            else if (curLia instanceof LiaIteImpl) result = ((LiaIteImpl) curLia).plusIte(result);
            else result = LiaStar.mkPlus(false, result, curLia);
          }
        }
        return (result == null) ? mkConst(false, 0) : result;
      }
      case MULTIPLY -> {
        LiaStar result = null;
        final List<UTerm> subt = exp.subTerms();
        for (UTerm t : subt) {
          final LiaStar curLia = transUexpNoSum(t, uVarsToLiaVars);
          if (curLia instanceof LiaConstImpl) {
            long value = ((LiaConstImpl)curLia).getValue();
            if ( value == 0 )
              return mkConst(false, 0);
            if (value == 1)
              continue;
          }
          if (result == null) result = curLia;
          else {
            if (result instanceof LiaIteImpl) result = ((LiaIteImpl) result).MultIte(curLia);
            else if (curLia instanceof LiaIteImpl) result = ((LiaIteImpl) curLia).MultIte(result);
            else result = LiaStar.mkMult(false, result, curLia);
          }
        }
        return (result == null) ? mkConst(false, 1) : result;
      }
      case NEGATION -> {
        final UTerm body = ((UNeg) exp).body();
        final LiaStar cond = LiaStar.mkEq(false, transUexpNoSum(body, uVarsToLiaVars), LiaStar.mkConst(false, 0));
        return LiaStar.mkIte(false, cond, LiaStar.mkConst(false, 1), LiaStar.mkConst(false, 0));
      }
      case SQUASH -> {
        final UTerm body = ((USquash) exp).body();
        final LiaStar cond = LiaStar.mkEq(false, transUexpNoSum(body, uVarsToLiaVars), LiaStar.mkConst(false, 0));
        return LiaStar.mkIte(false, cond, LiaStar.mkConst(false, 0), LiaStar.mkConst(false, 1));
      }
      case CONST -> {
        return LiaStar.mkConst(false, ((UConst) exp).value());
      }
      case TABLE -> {
        final UTable table = (UTable) exp;
        final String tblName = table.tableName().toString();
        final UVar tblVar = table.var();
        final LiaStar lVar = getOrRegisterLiaForUVar(tblVar, uVarsToLiaVars);
        return LiaStar.mkFunc(false, tblName, lVar);
      }
      case PRED -> {
        final UPred pred = (UPred) exp;
        if (pred.isPredKind(UPred.PredKind.FUNC) && isPredOfVarArg(pred)) {
          // Case 1. [p(a(t))]
          final List<UVar> pArgs = UExprSupport.getPredVarArgs(pred);
          assert pArgs.size() == 1;
          final UVar predVar = pArgs.get(0); // a(t)
          final String predName = pred.predName().toString();
          final LiaStar lVar = getOrRegisterLiaForUVar(predVar, uVarsToLiaVars);
          final LiaStar funcLia = LiaStar.mkFunc(false, predName, lVar);
          return LiaStar.mkIte(false,
              LiaStar.mkEq(false, funcLia, LiaStar.mkConst(false, 0)),
              LiaStar.mkConst(false, 0),
              LiaStar.mkConst(false, 1));
        } else if (pred.isBinaryPred()) {
          // Case 2. [U-expr0 <binary op> U-expr1]
          final LiaStar liaVar0 = transUexpNoSum(pred.args().get(0), uVarsToLiaVars);
          final LiaStar liaVar1 = transUexpNoSum(pred.args().get(1), uVarsToLiaVars);

          if (liaVar0 instanceof LiaConstImpl && liaVar1 instanceof LiaConstImpl) {
            long value0 = ((LiaConstImpl)liaVar0).getValue();
            long value1 = ((LiaConstImpl)liaVar1).getValue();
            boolean b = switch (pred.predKind()) {
              case EQ -> value0 == value1;
              case NEQ -> value0 != value1;
              case LE -> value0 <= value1;
              case LT -> value0 < value1;
              case GE -> value0 >= value1;
              case GT -> value0 > value1;
              default -> throw new IllegalArgumentException("unsupported predicate in Uexpr.");
            };
            return b ? mkConst(false, 1) : mkConst(false, 0);
          }

          final LiaStar target = switch (pred.predKind()) {
            case EQ -> LiaStar.mkEq(false, liaVar0, liaVar1);
            case NEQ -> LiaStar.mkNot(false, LiaStar.mkEq(false, liaVar0, liaVar1));
            case LE -> LiaStar.mkLe(false, liaVar0, liaVar1);
            case LT -> LiaStar.mkLt(false, liaVar0, liaVar1);
            case GE -> LiaStar.mkLe(false, liaVar1, liaVar0);
            case GT -> LiaStar.mkLt(false, liaVar1, liaVar0);
            default -> throw new IllegalArgumentException("unsupported predicate in Uexpr.");
          };
          return LiaStar.mkIte(false, target,
              LiaStar.mkConst(false, 1),
              LiaStar.mkConst(false, 0));
        } else {
          throw new UnsupportedOperationException("unsupported UPred var type.");
        }
      }
      case VAR -> {
        return getOrRegisterLiaForUVar(((UVarTerm) exp).var(), uVarsToLiaVars);
      }
      case STRING -> {
        return LiaStar.mkString(false, ((UString) exp).value());
      }
      case FUNC -> {
        UFunc func = (UFunc) exp;
        String funcName = func.funcName().toString();
        // in_list_N
        if (PredefinedFunctions.belongsToFamily(func, PredefinedFunctions.NAME_IN_LIST)) {
          List<LiaStar> liaOps = new ArrayList<>();
          List<UTerm> args = exp.subTerms();
          for (UTerm arg : args) {
            LiaStar liaOp = transUexpNoSum(arg, uVarsToLiaVars);
            liaOps.add(liaOp);
          }
          return LiaStar.mkFunc(false, funcName, liaOps);
        }
        // other functions
        switch (funcName) {
          case PredefinedFunctions.NAME_LIKE: {
            assert exp.subTerms().size() == 2;
            UTerm op0 = exp.subTerms().get(0);
            UTerm op1 = exp.subTerms().get(1);
            LiaStar liaOp0 = transUexpNoSum(op0, uVarsToLiaVars);
            LiaStar liaOp1 = transUexpNoSum(op1, uVarsToLiaVars);
            return LiaStar.mkFunc(false, PredefinedFunctions.NAME_LIKE, List.of(liaOp0, liaOp1));
          }
          default: {
            throw new UnsupportedOperationException("unsupported function: " + funcName);
          }
        }
      }
      default -> {
        throw new IllegalArgumentException("unsupported Uexpr type.");
      }
    }
  }

  LiaStar uexpWOSumToLiastar(UTerm t1, UTerm t2) {
    final Map<UVar, String> varMap = new HashMap<>();
    return LiaStar.mkNot(false, LiaStar.mkEq(false, transUexpNoSum(t1, varMap), transUexpNoSum(t2, varMap)));
  }

  String newUliaVarName() {
    return liaVarName.next();
  }

  // TODO: >=3 equal summations are not unified "correctly"
  void unifyEqualSummations(ArrayList<UTerm> sumList) {
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
    for (UVar v : s1) {
      if (s2.contains(v)) {
        return true;
      }
    }
    return false;
  }

  static ArrayList<HashSet<UVar>> buildEqRelation(Set<Pair<UVar, UVar>> eqVarPairs) {
    ArrayList<HashSet<UVar>> eqRels = new ArrayList<>();
    for (Pair<UVar, UVar> pair : eqVarPairs) {
      UVar v1 = pair.getLeft();
      UVar v2 = pair.getRight();
      HashSet<UVar> targetSet = null;
      for (int i = 0; i < eqRels.size(); ++ i) {
        HashSet<UVar> eqRel = eqRels.get(i);
        if (eqRel.contains(v1) || eqRel.contains(v2)) {
          if (targetSet == null) {
            targetSet = eqRel;
          } else {
            targetSet.addAll(eqRel);
            eqRel.clear();
          }
          targetSet.add(v1.copy());
          targetSet.add(v2.copy());
        }
      }
      if (targetSet == null) {
        HashSet<UVar> eqRel = new HashSet<>();
        eqRel.add(v1.copy());
        eqRel.add(v2.copy());
        eqRels.add(eqRel);
      }
    }

    ArrayList<HashSet<UVar>> result = new ArrayList<>();
    for (HashSet<UVar> s : eqRels) {
      if (!s.isEmpty()) {
        result.add(s);
      }
    }
    return result;
  }

  public static boolean hasFreeTuple(UVar v, HashSet<UVar> freeTuples) {
    switch (v.kind()) {
      case PROJ -> {
        for (UVar arg : v.args()) {
          if (hasFreeTuple(arg, freeTuples)) {
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
    for (UVar v : vars) {
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
        for (UTerm subterm : term.subTerms()) {
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
        for (UTerm subterm : term.subTerms()) {
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
    for (UTerm term : sumList) {
      result = result + computeTargetTupleScoreForOneUTerm(term, curSet, targetTuple, existingTerms);
    }
    return result;
  }

  UVar buildTargetTuplesForOneEqrel(ArrayList<UTerm> sumList, HashSet<UVar> curSet, HashSet<UVar> freeTuples, Set<UTerm> existingTerms) {
    HashSet<UVar> targetTuples = new HashSet<>();
    for (UVar v : curSet) {
      if (existingTerms.contains(UVarTerm.mk(v))) {
        targetTuples.add(v.copy());
      }
    }
    if (!targetTuples.isEmpty()) {
      int maxScore = -1;
      UVar targetTuple = null;
      for (UVar var : targetTuples) {
        int curScore = computeScoreForTargetTuple(sumList, curSet, var, existingTerms);
        if (curScore > maxScore) {
          targetTuple = var;
          maxScore = curScore;
        }
      }
      return targetTuple;
    }

    targetTuples = new HashSet<>();
    for (UVar v : curSet) {
      if (hasFreeTuple(v, freeTuples)) {
        targetTuples.add(v.copy());
      }
    }
    if (!targetTuples.isEmpty()) {
      int maxScore = -1;
      UVar targetTuple = null;
      for (UVar var : targetTuples) {
        int curScore = computeScoreForTargetTuple(sumList, curSet, var, existingTerms);
        if (curScore > maxScore) {
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
    for (int i = 0; i < eqRels.size(); ++ i) {
      HashSet<UVar> curSet = eqRels.get(i);
      targetTuples.add(buildTargetTuplesForOneEqrel(sumList, curSet, freeTuples, existingTerms));
    }
    return targetTuples;
  }

  void addEqSetToRels(ArrayList<HashSet<UVar>> eqRels, HashSet<UVar> newSet) {
    int i = 0;
    for ( ; i < eqRels.size(); ++ i) {
      HashSet<UVar> curSet = eqRels.get(i);
      boolean succeed = false;
      for (UVar v : newSet) {
        if (curSet.contains(v)) {
          curSet.addAll(newSet);
          succeed = true;
          break;
        }
      }
      if (succeed)
        break;
    }
    if (i == eqRels.size()) {
      eqRels.add(newSet);
    }
  }

  void addVarToEqRel(ArrayList<HashSet<UVar>> eqRels, UVar v, Set<UTerm> existingTerms) {
    switch (v.kind()) {
      case PROJ -> {
        UName attrName = UName.mk(v.name().toString());
        UVar innerTuple = v.args()[0];
        for (int i = 0; i < eqRels.size(); ++ i) {
          HashSet<UVar> curSet = eqRels.get(i);
          if (curSet.contains(innerTuple)) {
            HashSet<UVar> newSet = new HashSet<>();
            newSet.add(v);
            for (UVar tuple : curSet) {
              UVar eqTuple = (tuple.kind() == UVar.VarKind.BASE) ? tuple.copy() : tuple.args()[0].copy();
              newSet.add(UVar.mkProj(attrName,eqTuple));
            }
            addEqSetToRels(eqRels, newSet);
            break;
          } else if (any(curSet, arg -> arg.isUsing(innerTuple))) {
            HashSet<UVar> newSet = new HashSet<>();
            newSet.add(v);
            for (UVar tuple : curSet) {
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
        if (thisSet == null) continue;

        for (int j = i + 1; j < eqRels.size(); ++ j) {
          HashSet<UVar> thatSet = eqRels.get(j);
          if (thatSet == null) continue;

          if (overlap(thisSet, thatSet)) {
            thisSet.addAll(thatSet);
            eqRels.set(i, thisSet);
            eqRels.set(j, null);
            modified = true;
          }
        }
      }
    }

    for (int i = 0; i < eqRels.size(); ++ i) {
      if (eqRels.get(i) == null) {
        eqRels.remove(i);
        i --;
      }
    }
  }

  void expandEqRelation(ArrayList<HashSet<UVar>> eqRels, ArrayList<UTerm> sumList, Set<UTerm> existingTerms) {
    HashSet<UVar> tuples = new HashSet<>();
    for (UTerm t : sumList) {
      tuples.addAll(searchFreeUnaryVars(t));
    }
    for (UVar v : tuples) {
      addVarToEqRel(eqRels, v, existingTerms);
    }

    mergeEqRels(eqRels);
  }

  void rewriteWithEqRelation(UTerm cur, ArrayList<HashSet<UVar>> eqRels, ArrayList<UVar> targetTuples) {
    for (int j = 0; j < eqRels.size(); ++ j) {
      HashSet<UVar> curSet = eqRels.get(j);
      UVar targetTuple = targetTuples.get(j);
      for (UVar v : curSet) {
        if (!v.equals(targetTuple)) {
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
    for (int j = 0; j < eqRels.size(); ++ j) {
      HashSet<UVar> curSet = eqRels.get(j);
      UVar targetTuple = targetTuples.get(j);
      for (UVar v : curSet) {
        if (!v.equals(targetTuple)) {
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
    for (UTerm t : sumList) {
      if (!(t instanceof UMul)) {
        return false;
      }
    }
    return true;
  }

  boolean isUsingTuples(UVar var, Set<UVar> freeTuples) {
    for (UVar v : freeTuples) {
      if (var.isUsing(v)) {
        return true;
      }
    }
    return false;
  }

  void rewriteSumsWithIndPred(ArrayList<UTerm> sumList, HashSet<UVar> freeTuples, Set<UTerm> existingTerms) {
    if (!allIsMult(sumList)) {
      return;
    }
    for (UTerm curExp : sumList) {
      Set<Pair<UVar, UVar>> eqVars = collectPredicatesFromOneTerm(curExp);
      UMul tmp = (UMul) curExp;
      for (UTerm term : tmp.subTerms()) {
        if (term instanceof UNeg) {
          term = ((UNeg) term).body();
        } else if (term instanceof USquash) {
          term = ((USquash) term).body();
        }
        if (!(term instanceof UPred))
          continue;
        UPred pred = (UPred) term;
        if (pred.isPredKind(UPred.PredKind.FUNC) && isPredOfVarArg(pred)) {
          for (Pair<UVar, UVar> pair : eqVars) {
            UVar left = pair.getLeft();
            UVar right = pair.getRight();
            if (isUsingTuples(left, freeTuples)) {
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

  private Set<UTerm> getSubTermsOtherThanVarEq(UMul t) {
    Set<UTerm> terms = new HashSet<>();
    for (UTerm sub : t.subTerms()) {
      // [v1 = v2]
      if (sub instanceof UPred pred
              && pred.isPredKind(UPred.PredKind.EQ)
              && pred.args().get(0).kind() == VAR
              && pred.args().get(1).kind() == VAR) {
        continue;
      }
      terms.add(sub);
    }
    return terms;
  }

  /* Whether the sets of subterms other than [v1 = v2] equal */
  private boolean equalsExceptVarEqPreds(UMul t1, UMul t2) {
    Set<UTerm> s1 = getSubTermsOtherThanVarEq(t1);
    Set<UTerm> s2 = getSubTermsOtherThanVarEq(t2);
    return s1.equals(s2);
  }

  boolean instantiationWithPredicate(ArrayList<UTerm> sumList, HashSet<UVar> freeTuples, Set<UTerm> existingTerms) {

    if (sumList.size() == 2 && allIsMult(sumList)) {
      if (equalsExceptVarEqPreds((UMul) sumList.get(0), (UMul) sumList.get(1)))
        return true;
    }

    ArrayList<HashSet<UVar>> eqRels = collectPredicates(sumList);
    mergeEqRels(eqRels);
//    if(eqRels.isEmpty())
//      rewriteSumsWithIndPred(sumList, freeTuples, existingTerms);
    if (eqRels.isEmpty() && (sumList.size() > 1)) {
      for (UTerm term : sumList) {
        ArrayList<UTerm> tmp = new ArrayList<>();
        tmp.add(term);
        instantiationWithPredicate(tmp, freeTuples, existingTerms);
      }
    }
    if (eqRels.isEmpty() && !allIsMult(sumList)) {
      return false;
    }
    expandEqRelation(eqRels, sumList, existingTerms);
    ArrayList<UVar> targetTuples = buildTargetTuples(sumList, eqRels, freeTuples, existingTerms);

    for (int i = 0; i < sumList.size(); ++i) {
      UTerm cur = sumList.get(i);
      if (sumList.size() == 1) {
        rewriteSingleUTermWithEqRelation(cur, eqRels, targetTuples);
      } else {
        rewriteWithEqRelation(cur, eqRels, targetTuples);
      }
    }
    // when there is only one summation, we still need to perform instantiation with tuple
    return (sumList.size() > 1);
  }

  boolean instantiationWithTuple(ArrayList<UTerm> sumList, UVar commonTuple, HashSet<UVar> freeTuples) {
    if (sumList.size() > 1)
      return false;
    for (UTerm t : sumList) {
      if (t instanceof USum) {
        return false;
      }
    }
    for (int i = 0; i < sumList.size(); ++ i) {
      sumList.set(i, instantiationOneSumWithTuple(sumList.get(i), commonTuple, freeTuples));
    }
    return true;
  }


  Set<UVar> collectBaseTuple(Set<UVar> tuples) {
    Set<UVar> baseTuples = new HashSet<>();
    for (UVar v : tuples) {
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
    for (UVar v : freeTuples) {
      if (v.equals(sumTuple)) {
        continue;
      }
      terms.add(body.replaceVar(sumTuple, v,false).copy());
    }
    HashSet<UVar> boundVars = new HashSet<>();
    boundVars.add(sumTuple);
    terms.add(USum.mk(boundVars, body.copy()));
    return UAdd.mk(terms);
  }

  LiaStar sumsToLiaStar(
      boolean isInner,
      boolean instWithTuple,
      ArrayList<UTerm> sumList,
      ArrayList<String> sumVarList,
      Set<Integer> sumIndexSet1,
      Set<Integer> sumIndexSet2,
      HashMap<UTerm, String> termVarMap,
      HashSet<UVar> freeTuples
  ) {

    ArrayList<UTerm> newSumList = new ArrayList<>();
    copySumList(sumList, newSumList);

    UVar commonTuple;
    commonTuple = matcher.injectCommonTuple(newSumList, sumIndexSet1, sumIndexSet2);

    alignSummation(newSumList, commonTuple);
    boolean flag = instantiationWithPredicate(newSumList, freeTuples, termVarMap.keySet());
    unifyEqualSummations(newSumList);
    boolean ifInstWithTuple = false;
    if (!flag && instWithTuple) {
      ifInstWithTuple = instantiationWithTuple(newSumList, commonTuple, freeTuples);
    }

    final ArrayList<UTerm> subSums = new ArrayList<>();
    final ArrayList<String> subVars = new ArrayList<>();
    Set<Integer> subSumIndexSet1 = new HashSet<>();
    Set<Integer> subSumIndexSet2 = new HashSet<>();
    replaceSumsInList(newSumList, sumIndexSet1, sumIndexSet2, subSums, subVars, subSumIndexSet1, subSumIndexSet2);
    LiaStar constraints = null;
    ArrayList<String> innerVector = new ArrayList<>();
    HashSet<UVarTerm> isNullTuples = new HashSet<>();
    Set<LiaVarImpl> stringVars = new HashSet<>();
    // equations
    for (int i = 0; i < sumVarList.size(); ++i) {
      String innerVarName = newUliaVarName();
      innerVector.add(innerVarName);
      LiaStar equation = transUexpWithoutSum(true, newSumList.get(i), termVarMap, isNullTuples, stringVars);
      if (ifInstWithTuple) {
        equation = LiaStar.mkEq(true, LiaStar.mkVar(true, sumVarList.get(i)), equation);
      } else {
        equation = LiaStar.mkEq(true, LiaStar.mkVar(true, innerVarName), equation);
      }
      if (constraints == null) {
        constraints = equation;
      } else {
        constraints = LiaStar.mkAnd(true, constraints, equation);
      }
    }
    // IsNull constraints
    LiaStar isNullConstraints = isNullCongruence(termVarMap, isNullTuples);
    if (isNullConstraints != null)
      constraints = LiaStar.mkAnd(true, constraints, isNullConstraints);
    if (!subSums.isEmpty()) {
      if (!ifInstWithTuple) {
        freeTuples.add(commonTuple);
      }
      constraints = mkAnd(true, constraints,
          sumsToLiaStar(true, !ifInstWithTuple, subSums, subVars, subSumIndexSet1, subSumIndexSet2, termVarMap, freeTuples)
      );
    }
    // string var constraints
    LiaStar stringVarConstraints = null;
    Set<LiaVarImpl> usedStringVars = new HashSet<>();
    for (LiaVarImpl v1 : stringVars) {
      usedStringVars.add(v1);
      for (LiaVarImpl v2 : stringVars) {
        if (!usedStringVars.contains(v2)) {
          LiaStar neq = LiaStar.mkNot(true, LiaStar.mkEq(true, v1, v2));
          if (stringVarConstraints == null)
            stringVarConstraints = neq;
          else
            stringVarConstraints = LiaStar.mkAnd(true, stringVarConstraints, neq);
        }
      }
    }
    constraints = LiaStar.mkAnd(true, constraints, stringVarConstraints);

    if (ifInstWithTuple) {
      return constraints;
    } else {
      LiaSumImpl result = (LiaSumImpl) mkSum(isInner, sumVarList, innerVector, constraints);
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

  private static LiaStar isNullCongruence(HashMap<UTerm, String> termVarMap, HashSet<UVarTerm> isNullTuples) {
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
    LiaStar result = null;
    for (UVarTerm v1 : isNullTuples) {
      String var1 = termVarMap.get(v1);
      assert var1 != null;
      ArrayList<UTerm> isNullarg1 = new ArrayList<>();
      isNullarg1.add(v1);
      String isNullVar1 = termVarMap.get(UPred.mk(UPred.PredKind.FUNC, NAME_IS_NULL, isNullarg1));
      LiaVarImpl liavar1 = (LiaVarImpl) LiaStar.mkVar(true, var1);
      LiaVarImpl liaIsNullvar1 = (LiaVarImpl) LiaStar.mkVar(true, isNullVar1);
      for (UVarTerm v2 : existingIsNullTuples) {
        String var2 = termVarMap.get(v2);
        assert var2 != null;
        ArrayList<UTerm> isNullarg2 = new ArrayList<>();
        isNullarg2.add(v2);
        String isNullVar2 = termVarMap.get(UPred.mk(UPred.PredKind.FUNC, NAME_IS_NULL, isNullarg2));
        LiaVarImpl liavar2 = (LiaVarImpl) LiaStar.mkVar(true, var2);
        LiaVarImpl liaIsNullvar2 = (LiaVarImpl) LiaStar.mkVar(true, isNullVar2);
        LiaStar tmp = LiaStar.mkEq(true,
            liaIsNullvar1,
            LiaStar.mkIte(true, LiaStar.mkEq(true, liavar1, liavar2), liaIsNullvar2, liaIsNullvar1)
          );
//        Liastar tmp = Liastar.mkOr(true,
//            Liastar.mkNot(true, ),
//            Liastar.mkEq(true, liaIsNullvar1, liaIsNullvar2));
        result = (result == null) ? tmp : LiaStar.mkAnd(true, result, tmp) ;
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

  void copySumList(List<UTerm> sums, List<UTerm> newSums) {
    for (int i = 0; i < sums.size(); ++ i) {
      newSums.add(sums.get(i).copy());
    }
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
    for (Pair<UVar, UVar> pair : s1) {
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
    if (curExp instanceof USquash) {
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
    } else if (curExp instanceof UAdd) {
      List<UTerm> subts = curExp.subTerms();
      HashSet<Pair<UVar, UVar>> eqRel = null;
      for (UTerm t : subts) {
        HashSet<Pair<UVar, UVar>> tmp = collectPredicatesFromOneTerm(t);
        if (eqRel == null) {
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
        if (j == i) {
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
    for (UVar v : set1) {
      if (set2.contains(v)) {
        result.add(v);
      }
    }
    return result;
  }

  static ArrayList<HashSet<UVar>> mergeEqRels(ArrayList<HashSet<UVar>> rel1, ArrayList<HashSet<UVar>> rel2) {
    if (rel1.size() > rel2.size()) {
      return mergeEqRels(rel2, rel1);
    }
    ArrayList<HashSet<UVar>> result = new ArrayList<>();
    for (HashSet<UVar> thisSet : rel1) {
      HashSet<UVar> target = null;
      for (HashSet<UVar> thatSet : rel2) {
        HashSet<UVar> tmp = mergeSets(thisSet, thatSet);
        if (tmp.size() > 1) {
          target = thatSet;
          result.add(tmp);
          break;
        }
      }
      if (target != null) {
        rel2.remove(target);
      }
    }

    return result;
  }


  static ArrayList<HashSet<UVar>> analyseEqRels(ArrayList<Set<Pair<UVar, UVar>>> allEqVars) {
    if (allEqVars.isEmpty()) {
      return new ArrayList<>();
    }
    ArrayList<HashSet<UVar>> result = buildEqRelation(allEqVars.get(0));
    for (int i = 1; i < allEqVars.size(); ++ i) {
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

  /**
   * Given a list of terms ("list") and two sets ("indices1" and "indices2")
   * that include references (integers) to those terms,
   * replace summations in the terms with lia vars,
   * output the mapping to two lists ("subSums" and "subVars")
   * and two new sets ("subSumIndices1" and "subSumIndices2")
   * so that each summation that occurs in a term referenced by "indicesN"
   * is in "subSumIndicesN".
   */
  void replaceSumsInList(
      List<UTerm> list,
      Set<Integer> indices1, Set<Integer> indices2,
      List<UTerm> subSums, List<String> subVars,
      Set<Integer> subSumIndices1, Set<Integer> subSumIndices2) {
    Map<USum, String> sumMap = new HashMap<>();
    Set<USum> subSums1 = new HashSet<>(), subSums2 = new HashSet<>();
    for (int i = 0; i < list.size(); ++i) {
      // For each term, replace summations within it
      Set<USum> tmpSumSet = new HashSet<>();
      list.set(i, replaceSummations(sumMap, tmpSumSet, list.get(i)));
      // collect replaced summations on both sides
      if (indices1.contains(i)) subSums1.addAll(tmpSumSet);
      if (indices2.contains(i)) subSums2.addAll(tmpSumSet);
    }
    // convert map into two lists (keys and values)
    for (Map.Entry<USum, String> entry : sumMap.entrySet()) {
      subSums.add(entry.getKey());
      subVars.add(entry.getValue());
    }
    // turn a summation set to an index set so that:
    //   if i is in subSumIndices2N,
    //   then subSums[i] is a summation in queryN (N = 1 or 2)
    subSumIndices1.addAll(subSums1.stream().map(subSums::indexOf).collect(Collectors.toSet()));
    subSumIndices2.addAll(subSums2.stream().map(subSums::indexOf).collect(Collectors.toSet()));
  }

  UTerm replaceSummations(Map<USum, String> sumMap,
                          Set<USum> sums, UTerm uexp) {
    switch (uexp.kind()) {
      case SUMMATION:
        sums.add((USum) uexp);
        if (sumMap.containsKey(uexp)) return ULiaVar.mk(sumMap.get(uexp));
        final String sumName = newUliaVarName();
        final ULiaVar newVar = ULiaVar.mk(sumName);
        sumMap.put((USum) uexp, sumName);
        return newVar;
      case MULTIPLY, ADD, PRED, FUNC: {
        final List<UTerm> subTerms = uexp.subTerms();
        final List<UTerm> newSubTerms = new ArrayList<>();
        for (UTerm t : subTerms) {
          newSubTerms.add(replaceSummations(sumMap, sums, t));
        }
        return switch (uexp.kind()) {
          case MULTIPLY -> UMul.mk(newSubTerms);
          case ADD -> UAdd.mk(newSubTerms);
          case FUNC -> UFunc.mk(((UFunc)uexp).funcKind(), ((UFunc)uexp).funcName(), newSubTerms);
          default -> UPred.mk(((UPred) uexp).predKind(), ((UPred) uexp).predName(), newSubTerms);
        };
      }
      case NEGATION:
        return UNeg.mk(replaceSummations(sumMap, sums, ((UNeg) uexp).body()));
      case SQUASH:
        return USquash.mk(replaceSummations(sumMap, sums, ((USquash) uexp).body()));
      default:
        return uexp;
    }
  }

  void alignSummation(List<UTerm> sums, UVar commonTuple) {
    if (sums.size() <= 1)
      return;

    for (int i = 0; i < sums.size(); ++i) {
      UTerm term = sums.get(i);
      if (term instanceof UMul && term.subTerms().size() == 1) {
        sums.set(i, term.subTerms().get(0));
      }
    }

    boolean hasSquashSum = false;
    boolean hasNoSquashSum = false;
    for (UTerm t : sums) {
      if (t instanceof USquash && ((USquash) t).body() instanceof USum) {
        hasSquashSum = true;
      }
      else if (t instanceof USquash && !(((USquash) t).body() instanceof USum)) {
        hasNoSquashSum = true;
      }
    }

    if (hasSquashSum && hasNoSquashSum) {
      for (int i = 0; i < sums.size(); ++i) {
        UTerm term = sums.get(i);
        if (term instanceof USquash squash && squash.body() instanceof USum sum) {
          UTerm alignedTerm = splitSummation(sum);
          if (alignedTerm instanceof UMul) {
            for (int j = 0; j < alignedTerm.subTerms().size(); ++j) {
              UTerm t = alignedTerm.subTerms().get(j);
              if (t instanceof USum tmp && tmp.boundedVars().size() == 1) {
                UVar bVar = new ArrayList<>(tmp.boundedVars()).get(0);
                UTerm body = tmp.body();
                alignedTerm.subTerms().set(j, UAdd.mk(tmp.copy(), body.replaceVar(bVar, commonTuple, false)));
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

  LiaStar transUexpWithoutSum(boolean innerStar,
                              UTerm exp,
                              Map<UTerm, String> uTermToLiaVar,
                              HashSet<UVarTerm> isnullTuples) {
    return transUexpWithoutSum(innerStar, exp, uTermToLiaVar, isnullTuples, null);
  }

  // summations in exp have been replaced by new variables
  // Then transUexpWithoutSum translates exp into LIA formula
  // uTermToLiaVar is used to replace the same terms with same variables
  LiaStar transUexpWithoutSum(boolean innerStar,
                              UTerm exp,
                              Map<UTerm, String> uTermToLiaVar,
                              HashSet<UVarTerm> isnullTuples,
                              Set<LiaVarImpl> stringVars) {
    switch (exp.kind()) {
      case SUMMATION -> throw new UnsupportedOperationException("should not have summation when transforming to Lia!");
      case ADD -> {
        LiaStar result = null;
        final List<UTerm> subTerms = exp.subTerms();
        for (UTerm t : subTerms) {
          LiaStar curLia = transUexpWithoutSum(innerStar, t, uTermToLiaVar, isnullTuples, stringVars);
          curLia = curLia.simplifyIte();
          if (result == null) {
            result = curLia;
          } else if (result instanceof LiaIteImpl) {
            result = ((LiaIteImpl)result).plusIte(curLia);
          } else if (curLia instanceof LiaIteImpl) {
            result = ((LiaIteImpl)curLia).plusIte(result);
          } else {
            result = LiaStar.mkPlus(innerStar, result, curLia);
          }
        }
        return result;
      }
      case MULTIPLY -> {
        LiaStar result = null;
        final List<UTerm> subTerms = exp.subTerms();
        LiaStar iteNonzeroCond = null;
        for (UTerm t : subTerms) {
          LiaStar curLia = transUexpWithoutSum(innerStar, t, uTermToLiaVar, isnullTuples, stringVars);
          LiaStar[] condOpArray = new LiaStar[2];
          boolean hasZeroIte = ishasZeroIte(innerStar, curLia, condOpArray);
          if (hasZeroIte) {
            LiaStar cond = condOpArray[0];
            LiaStar op = condOpArray[1];
            iteNonzeroCond = (iteNonzeroCond == null) ? cond : mkAnd(innerStar, iteNonzeroCond, cond);
          } else {
            if (result == null) result = curLia;
            else {
              if (result instanceof LiaIteImpl) result = ((LiaIteImpl) result).MultIte(curLia);
              else if (curLia instanceof LiaIteImpl) result = ((LiaIteImpl) curLia).MultIte(result);
              else result = LiaStar.mkMult(innerStar, result, curLia);
            }
          }
        }
        if (iteNonzeroCond != null) {
          if (result == null) {
            result = mkConst(innerStar, 1);
          }
          result = mkIte(innerStar, iteNonzeroCond, result, mkConst(innerStar, 0));
        }
        return result;
      }
      case NEGATION, SQUASH -> {
        final UTerm body = ((UUnary) exp).body();
        final LiaStar cond =
            LiaStar.mkEq(
                innerStar,
                transUexpWithoutSum(innerStar, body, uTermToLiaVar, isnullTuples, stringVars),
                LiaStar.mkConst(innerStar, 0));
        return exp.kind() == NEGATION
            ? LiaStar.mkIte(innerStar, cond, LiaStar.mkConst(innerStar, 1), LiaStar.mkConst(innerStar, 0))
            : LiaStar.mkIte(innerStar, cond, LiaStar.mkConst(innerStar, 0), LiaStar.mkConst(innerStar, 1));
      }
      case CONST -> {
        return LiaStar.mkConst(false, ((UConst) exp).value());
      }
      case TABLE -> {
        final String varName = uTermToLiaVar.computeIfAbsent((UTable) exp, t -> newUliaVarName());
        return LiaStar.mkVar(innerStar, varName);
      }
      case PRED -> {
        // Case 1. ULiaVar
        if (exp instanceof ULiaVar) return LiaStar.mkVar(innerStar, exp.toString());
        final UPred pred = (UPred) exp;
        if (pred.isPredKind(UPred.PredKind.FUNC) && isPredOfVarArg(pred)) {
          // Case 2. [p(a(t))]. View `p(a(t))` as a variable
          final List<UVar> pArgs = UExprSupport.getPredVarArgs(pred);
          assert pArgs.size() == 1;
          uTermToLiaVar.computeIfAbsent(UVarTerm.mk(pArgs.get(0)), v -> newUliaVarName());
          final String varName = uTermToLiaVar.computeIfAbsent(pred, v -> newUliaVarName());
          final LiaStar liaVar = LiaStar.mkVar(innerStar, varName);
          if (pred.predName().equals(NAME_IS_NULL))
            isnullTuples.add(UVarTerm.mk(pArgs.get(0)));
          return LiaStar.mkIte(
              innerStar,
              LiaStar.mkEq(innerStar, liaVar, LiaStar.mkConst(innerStar, 0)),
              LiaStar.mkConst(innerStar, 0),
              LiaStar.mkConst(innerStar, 1));
        } else if (pred.isBinaryPred()) {
          // Case 3. [U-expr0 <binary op> U-expr1]
          final LiaStar liaVar0 = transUexpWithoutSum(innerStar, pred.args().get(0), uTermToLiaVar, isnullTuples, stringVars);
          final LiaStar liaVar1 = transUexpWithoutSum(innerStar, pred.args().get(1), uTermToLiaVar, isnullTuples, stringVars);
          final LiaStar target = switch (pred.predKind()) {
            case EQ -> LiaStar.mkEq(innerStar, liaVar0, liaVar1);
            case NEQ -> LiaStar.mkNot(innerStar, LiaStar.mkEq(innerStar, liaVar0, liaVar1));
            case LE -> LiaStar.mkLe(innerStar, liaVar0, liaVar1);
            case LT -> LiaStar.mkLt(innerStar, liaVar0, liaVar1);
            case GE -> LiaStar.mkLe(innerStar, liaVar1, liaVar0);
            case GT -> LiaStar.mkLt(innerStar, liaVar1, liaVar0);
            default -> throw new IllegalArgumentException("unsupported predicate in Uexpr.");
          };
          return LiaStar.mkIte(innerStar, target, LiaStar.mkConst(innerStar, 1), LiaStar.mkConst(innerStar, 0));
        } else {
          throw new UnsupportedOperationException("unsupported UPred var type.");
        }
      }
      case VAR, STRING -> {
        final String varName = uTermToLiaVar.computeIfAbsent(exp, v -> newUliaVarName());
        LiaVarImpl var = (LiaVarImpl) LiaStar.mkVar(innerStar, varName);
        if (exp instanceof UString && stringVars != null) stringVars.add(var);
        return var;
      }
      case FUNC -> {
        return transFuncNoSum(innerStar, (UFunc) exp, uTermToLiaVar, isnullTuples, stringVars);
      }
      default -> throw new UnsupportedOperationException("unsupported UTerm type.");
    }
  }

  private LiaStar transFuncNoSum(
          boolean innerStar,
          UFunc func,
          Map<UTerm, String> uTermToLiaVar,
          HashSet<UVarTerm> isnullTuples,
          Set<LiaVarImpl> stringVars) {
    // translate the function case by case
    final String funcName = func.funcName().toString();
    final int arity = func.args().size();
    // non-negative integral functions can be replaced with a var
    if (returnsNonNegativeInt(funcName, arity)) {
      final String varName = uTermToLiaVar.computeIfAbsent(func, t -> newUliaVarName());
      return LiaStar.mkVar(innerStar, varName);
    }
    // other functions are translated into different LIA terms
    // first translate function arguments
    final List<LiaStar> liaOps = new ArrayList<>();
    final List<UTerm> args = func.args();
    for (UTerm arg : args) {
      LiaStar liaOp = transUexpWithoutSum(innerStar, arg, uTermToLiaVar, isnullTuples, stringVars);
      liaOps.add(liaOp);
    }
    // then translate the function
    if (DIVIDE.contains(funcName, arity)) {
      // division has a dedicated LIA expression type
      return LiaStar.mkDiv(innerStar, liaOps.get(0), liaOps.get(1));
    }
    return LiaStar.mkFunc(innerStar, funcName, liaOps);
  }

}

package wtune.superopt.liastar;

import com.microsoft.z3.*;
import wtune.superopt.util.PrettyBuilder;

import java.util.*;
import java.util.function.Function;

import static wtune.superopt.liastar.LiaOpType.*;


public abstract class Liastar {

  public boolean innerStar = false;

  private static ThreadLocal<Integer> freshVarId = new ThreadLocal<Integer>() {
    public Integer initialValue() {
      return 0;
    }
  };

  private static final Integer dnfTimeout = 2000000;
  private static ThreadLocal<Integer> dnfStartTime  = new ThreadLocal<Integer>() {
    public Integer initialValue() {
      return 0;
    }
  };

  public static void setDnfStartTime() {
    dnfStartTime.set(0);
  }

  public Liastar mergeSameVars() {return this;}

  public static boolean isDnfTimeout() {
    dnfStartTime.set(dnfStartTime.get() + 1);
    return (dnfStartTime.get() > dnfTimeout);
  }

  public abstract boolean isLia();

  public abstract Liastar deepcopy();

  public abstract Liastar multToBin(int n);

  public abstract Liastar simplifyMult(HashMap<Liastar, String> multToVar);

  public abstract LiaOpType getType();


  public abstract Liastar mergeMult(HashMap<LiamultImpl, String> multToVar);

  public abstract int embeddingLayers();

  public static String newId() {
    freshVarId.set(freshVarId.get() + 1);
    return String.valueOf(freshVarId.get());
  }

  public static String resetId() {
    freshVarId.set(0);
    return String.valueOf(freshVarId.get());
  }

  public static String newVarName() {
    return "var" + newId();
  }

  public abstract Set<String> collectVarSet();

  public abstract Liastar expandStar() throws Exception;

  public Liastar liaAndConcat(Liastar[] array) {
    Liastar res = null;
    for(int i = 0; i < array.length; ++ i) {
      if(array[i] != null) {
        if(res == null)
          res = array[i];
        else
          res = new LiaandImpl(res, array[i]);
        res.innerStar = true;
      }
    }

    return res;
  }

  public abstract Expr transToSMT(Context ctx, HashMap<String, IntExpr> varsName);

  final class EstimateResult {
    final Set<String> vars;
    final int n_extra;
    final int m;
    final double a;
    public EstimateResult(Set<String> vars, int n_extra, int m, double a) {
      this.vars = vars;
      this.n_extra = n_extra;
      this.m = m;
      this.a = a;
    }
  }

  public abstract EstimateResult estimate();

  public abstract Expr expandStarWithK(Context ctx, Solver sol, String suffix);

  public static Liastar mkAnd(boolean isInnerStar, Liastar a, Liastar b) {
    if(a == null && b == null) {
      assert false;
      return null;
    }
    else if(a == null && b != null)
      return b;
    else if(a != null && b == null)
      return a;
    else {
      Liastar result = new LiaandImpl(a, b);
      result.innerStar = isInnerStar;
      return result;
    }
  }

  public static Liastar mkConst(boolean isInnerStar, long c) {
    Liastar result = new LiaconstImpl(c);
    result.innerStar = isInnerStar;
    return result;
  }

  public static Liastar mkString(boolean isInnerStar, String v) {
    Liastar result = new LiastringImpl(v);
    result.innerStar = isInnerStar;
    return result;
  }

  public static Liastar mkEq(boolean isInnerStar, Liastar a, Liastar b) {
    Liastar result = new LiaeqImpl(a, b);
    result.innerStar = isInnerStar;
    return result;
  }

  public static Liastar mkIte(boolean isInnerStar, Liastar cond, Liastar op1, Liastar op2) {
    Liastar result = new LiaiteImpl(cond, op1, op2);
    result.innerStar = isInnerStar;
    return result;
  }

  public static Liastar mkLe(boolean isInnerStar, Liastar a, Liastar b) {
    Liastar result = new LialeImpl(a, b);
    result.innerStar = isInnerStar;
    return result;
  }

  public static Liastar mkLt(boolean isInnerStar, Liastar a, Liastar b) {
    Liastar result = new LialtImpl(a, b);
    result.innerStar = isInnerStar;
    return result;
  }

  public static Liastar mkMult(boolean isInnerStar, Liastar a, Liastar b) {
    Liastar result = new LiamultImpl(a, b);
    result.innerStar = isInnerStar;
    return result;
  }

  public static Liastar mkNot(boolean isInnerStar, Liastar a) {
    Liastar result = new LianotImpl(a);
    result.innerStar = isInnerStar;
    return result;
  }

  public static Liastar mkOr(boolean isInnerStar, Liastar a, Liastar b) {
    if(a == null && b == null) {
      assert false;
      return a;
    }
    else if(a == null) return b;
    else if(b == null) return a;
    else {
      Liastar result = new LiaorImpl(a, b);
      result.innerStar = isInnerStar;
      return result;
    }
  }

  public static Liastar mkPlus(boolean isInnerStar, Liastar a, Liastar b) {
    Liastar result = new LiaplusImpl(a, b);
    result.innerStar = isInnerStar;
    return result;
  }

  public static Liastar mkDiv(boolean isInnerStar, Liastar a, Liastar b) {
    Liastar result = new LiadivImpl(a, b);
    result.innerStar = isInnerStar;
    return result;
  }

  public static Liastar mkSum(boolean isInnerStar, ArrayList<String> outerVector, ArrayList<String> innerVector, Liastar a) {
    Liastar result = new LiasumImpl(outerVector, innerVector, a);
    result.innerStar = isInnerStar;
    return result;
  }

  public static Liastar mkFunc(boolean isInnerStar, String funcName, Liastar var) {
    Liastar result = new LiaFuncImpl(funcName, var);
    result.innerStar = isInnerStar;
    return result;
  }

  public static Liastar mkFunc(boolean isInnerStar, String funcName, List<Liastar> vars) {
    Liastar result = new LiaFuncImpl(funcName, vars);
    result.innerStar = isInnerStar;
    return result;
  }

  public static Liastar mkVar(boolean isInnerStar, String varName) {
    Liastar result = new LiavarImpl(varName);
    result.innerStar = isInnerStar;
    return result;
  }

  public abstract Set<String> getVars();

  public boolean isConstV(long v) {
    if(this instanceof LiaconstImpl)
      return ((LiaconstImpl) this).getValue() == v;
    else
      return false;
  }

  /** Transform a parameterized Lia formula to its DNF
   * @param activated: set `false` at the beginning
   * */
  public static Liastar paramLiaStar2DNF(Liastar formula, boolean activated) throws Exception {

    if(isDnfTimeout())
      throw new Exception("dnf timeout");

    if (formula == null) return null;

    // Do recursion from inner to outer (?)
    switch (formula.getType()) {
      // Logic op: OR, AND NOT
      case LOR -> {
        // Do nothing for f1 \/ f2
        final LiaorImpl or = (LiaorImpl) formula;
        or.operand1 = paramLiaStar2DNF(or.operand1, activated);
        or.operand2 = paramLiaStar2DNF(or.operand2, activated);
        return simplifyDNF(or);
//        return or;
      }
      case LAND -> {
        final LiaandImpl and = (LiaandImpl) formula;
        final boolean innerStar = and.innerStar;
        and.operand1 = paramLiaStar2DNF(and.operand1, activated);
        and.operand2 = paramLiaStar2DNF(and.operand2, activated);
        if (activated) {
          Liastar newLia = null;
          // if (and.operand1.getType() == LNOT && and.operand2.getType() == LNOT) {
            // ~f1 /\ ~f2 <=> f1 \/ f2
            // final Liastar subOp1 = ((LianotImpl) and.operand1).operand;
            // final Liastar subOp2 = ((LianotImpl) and.operand2).operand;
            // newLia = mkOr(innerStar, subOp1, subOp2);
          // }
          if (and.operand1.getType() == LOR || and.operand2.getType() == LOR) {
            // f /\ (f1 \/ f2) <=> (f /\ f1) \/ (f1 /\ f2)
            final LiaorImpl or = (LiaorImpl) (and.operand1.getType() == LOR? and.operand1 : and.operand2);
            final Liastar other = or == and.operand1 ? and.operand2 : and.operand1; // f
            newLia = mkOr(innerStar, mkAnd(innerStar, other, or.operand1), mkAnd(innerStar, other, or.operand2));
          }
          if (newLia != null) return paramLiaStar2DNF(newLia, activated);
        }
        return simplifyDNF(and);
//        return and;
      }
      case LNOT -> {
        // ~(~f) <=> f
        // ~(f1 /\ f2) <=> ~f1 \/ ~f2
        // ~(f1 \/ f2) <=> ~f1 /\ ~f2
        final LianotImpl not = (LianotImpl) formula;
        final boolean innerStar = not.innerStar;
        not.operand = paramLiaStar2DNF(not.operand, activated);
        if (activated) {
          Liastar newLia = null;
          switch (not.operand.getType()) {
            case LNOT -> newLia = ((LianotImpl) not.operand).operand;
            case LAND -> {
              final Liastar subOp1 = ((LiaandImpl) not.operand).operand1;
              final Liastar subOp2 = ((LiaandImpl) not.operand).operand2;
              newLia = mkOr(innerStar, mkNot(innerStar, subOp1), mkNot(innerStar, subOp2));
            }
            case LOR -> {
              final Liastar subOp1 = ((LiaorImpl) not.operand).operand1;
              final Liastar subOp2 = ((LiaorImpl) not.operand).operand2;
              newLia = mkAnd(innerStar, mkNot(innerStar, subOp1), mkNot(innerStar, subOp2));
            }
          }
          if (newLia != null) return paramLiaStar2DNF(newLia, activated);
        }
        return simplifyDNF(not);
//        return not;
      }
      // Arithmetic ops: EQ, LE, LT
      case LEQ-> {
        // a = ite(b, c, d) <=> (b /\ a = c) \/ (~b /\ a = d)
        final LiaeqImpl eq = (LiaeqImpl) formula;
//        eq.operand1 = paramLiaStar2DNF(eq.operand1, activated);
//        eq.operand2 = paramLiaStar2DNF(eq.operand2, activated);
        final boolean innerStar = eq.innerStar;
        if (activated && (eq.operand1.getType() == LITE || eq.operand2.getType() == LITE)) {
          final LiaiteImpl ite = (LiaiteImpl) (eq.operand1.getType() == LITE ? eq.operand1 : eq.operand2);
          final Liastar other = ite == eq.operand1 ? eq.operand2 : eq.operand1;

          final LiaandImpl and1 = (LiaandImpl)
              mkAnd(innerStar, ite.cond, mkEq(innerStar, other, ite.operand1));
          final LiaandImpl and2 = (LiaandImpl)
              mkAnd(innerStar, mkNot(innerStar, ite.cond), mkEq(innerStar, other, ite.operand2));
          final Liastar or = mkOr(innerStar, and1, and2);
          return or;
//          return paramLiaStar2DNF(or, activated);
        }
        return simplifyDNF(eq);
//        return eq;
      }
      case LLE-> {
        final LialeImpl le = (LialeImpl) formula;
//        le.operand1 = paramLiaStar2DNF(le.operand1, activated);
//        le.operand2 = paramLiaStar2DNF(le.operand2, activated);
        final boolean innerStar = le.innerStar;
        if (activated && (le.operand1.getType() == LITE || le.operand2.getType() == LITE)) {
          final LiaiteImpl ite = (LiaiteImpl) (le.operand1.getType() == LITE ? le.operand1 : le.operand2);
          final Liastar other = ite == le.operand1 ? le.operand2 : le.operand1;

          final LiaandImpl and1 = (LiaandImpl)
              mkAnd(innerStar, ite.cond, mkLe(innerStar, other, ite.operand1));
          final LiaandImpl and2 = (LiaandImpl)
              mkAnd(innerStar, mkNot(innerStar, ite.cond), mkLe(innerStar, other, ite.operand2));
          final Liastar or = mkOr(innerStar, and1, and2);
          return paramLiaStar2DNF(or, activated);
        }
        return simplifyDNF(le);
//        return le;
      }
      case LLT-> {
        final LialtImpl lt = (LialtImpl) formula;
//        lt.operand1 = paramLiaStar2DNF(lt.operand1, activated);
//        lt.operand2 = paramLiaStar2DNF(lt.operand2, activated);
        final boolean innerStar = lt.innerStar;
        if (activated && (lt.operand1.getType() == LITE || lt.operand2.getType() == LITE)) {
          final LiaiteImpl ite = (LiaiteImpl) (lt.operand1.getType() == LITE ? lt.operand1 : lt.operand2);
          final Liastar other = ite == lt.operand1 ? lt.operand2 : lt.operand1;

          final LiaandImpl and1 = (LiaandImpl)
              mkAnd(innerStar, ite.cond, mkLt(innerStar, other, ite.operand1));
          final LiaandImpl and2 = (LiaandImpl)
              mkAnd(innerStar, mkNot(innerStar, ite.cond), mkLt(innerStar, other, ite.operand2));
          final Liastar or = mkOr(innerStar, and1, and2);
          return paramLiaStar2DNF(or, activated);
        }
        return simplifyDNF(lt);
//        return lt;
      }
      // Simple terms: PLUS, MULT, ITE
      case LPLUS -> {
        final LiaplusImpl plus = (LiaplusImpl) formula;
//        plus.operand1 = paramLiaStar2DNF(plus.operand1, activated);
//        plus.operand2 = paramLiaStar2DNF(plus.operand2, activated);
//        return simplifyDNF(plus);
        return plus;
      }
      case LMULT -> {
        final LiamultImpl mult = (LiamultImpl) formula;
//        mult.operand1 = paramLiaStar2DNF(mult.operand1, activated);
//        mult.operand2 = paramLiaStar2DNF(mult.operand2, activated);
//        return simplifyDNF(mult);
        return mult;
      }
      case LITE -> {
        final LiaiteImpl ite = (LiaiteImpl) formula;
//        ite.cond = paramLiaStar2DNF(ite.cond, activated);
//        ite.operand1 = paramLiaStar2DNF(ite.operand1, activated);
//        ite.operand2 = paramLiaStar2DNF(ite.operand2, activated);
//        return simplifyDNF(ite);
        return ite;
//        return ite;
      }
      // SUM
//      case LSUM -> {
//        final LiasumImpl sum = (LiasumImpl) formula;
//        // Judge whether in a param LiaStar.
//        // If not, stop recursion, else, set activated for DNF rewrite
//        if (sum.constraints.isLia()) {
//          final Set<String> varSet = sum.constraints.collectVarSet();
//          if (all(varSet, v -> sum.innerVector.contains(v))) return sum;
//          activated = true;
//        }
//        sum.constraints = paramLiaStar2DNF(sum.constraints, activated);
//        return sum;
//      }
      // Atomic ones: FUNC
      case LFUNC -> {
        assert false;
        return null;
//        final LiaFuncImpl func = (LiaFuncImpl) formula;
//        func.var = paramLiaStar2DNF(func.var, activated);
//        return simplifyDNF(func);
      }
      default -> {
        return formula;
      }
    }
  }

  public void prepareInnervector(HashSet<String> vars) {
    return;
  }

  public HashSet<String> collectParams() {
    return new HashSet<>();
  }

  public Liastar removeParameter() {
    return this;
  }

  public Liastar removeParameterEager() {
    return this;
  }

  public Liastar pushUpParameter(HashSet<String> newVars) {
    return this;
  }

  public Liastar simplifyIte() {
    return this;
  }

  public static ArrayList<Liastar> decomposeDNF(Liastar f) {
    if(f.getType() == LiaOpType.LOR) {
      LiaorImpl tmp = (LiaorImpl) f;
      ArrayList<Liastar> result = decomposeDNF(tmp.operand1);
      result.addAll(decomposeDNF(tmp.operand2));
      return result;
    } else {
      ArrayList<Liastar> result = new ArrayList<>();
      result.add(f);
      return result;
    }
  }

  public boolean overLap(Set<String> s1, Set<String> s2) {
    for(String s : s1) {
      if(s2.contains(s)) {
        return true;
      }
    }
    return false;
  }

  public static void decomposeConjunction(Liastar formula, ArrayList<Liastar> literals) {
    if(formula.getType() == LiaOpType.LAND) {
      LiaandImpl tmp = (LiaandImpl) formula;
      decomposeConjunction(tmp.operand1, literals);
      decomposeConjunction(tmp.operand2, literals);
    } else {
      literals.add(formula);
    }
  }

  public static boolean isTrue(Liastar formula) {
    switch(formula.getType()) {
      case LNOT -> {
        LianotImpl tmp = (LianotImpl) formula;
        return isFalse(tmp.operand);
      }
      case LLT -> {
        LialtImpl tmp = (LialtImpl) formula;
        Liastar operand1 = tmp.operand1;
        Liastar operand2 = tmp.operand2;
        if((operand1 instanceof LiaconstImpl) && (operand2 instanceof LiaconstImpl)) {
          long const1 = ((LiaconstImpl)operand1).value;
          long const2 = ((LiaconstImpl)operand2).value;
          return (const1 < const2);
        }
        break;
      }
      case LLE -> {
        LialeImpl tmp = (LialeImpl) formula;
        Liastar operand1 = tmp.operand1;
        Liastar operand2 = tmp.operand2;
        if(operand1.equals(operand2)) {
          return true;
        }
        if((operand1 instanceof LiaconstImpl) && (operand2 instanceof LiaconstImpl)) {
          long const1 = ((LiaconstImpl)operand1).value;
          long const2 = ((LiaconstImpl)operand2).value;
          return (const1 <= const2);
        }
        break;
      }
      case LEQ -> {
        LiaeqImpl tmp = (LiaeqImpl) formula;
        Liastar operand1 = tmp.operand1;
        Liastar operand2 = tmp.operand2;
        return operand1.equals(operand2);
      }
      default -> {
        return false;
      }
    }
    return false;
  }

  public static  boolean isFalse(Liastar formula) {
    switch(formula.getType()) {
      case LNOT -> {
        LianotImpl tmp = (LianotImpl) formula;
        return isTrue(tmp.operand);
      }
      case LLT -> {
        LialtImpl tmp = (LialtImpl) formula;
        Liastar operand1 = tmp.operand1;
        Liastar operand2 = tmp.operand2;
        if(operand1.equals(operand2)) {
          return true;
        }
        if((operand1 instanceof LiaconstImpl) && (operand2 instanceof LiaconstImpl)) {
          long const1 = ((LiaconstImpl)operand1).value;
          long const2 = ((LiaconstImpl)operand2).value;
          return !(const1 < const2);
        }
        break;
      }
      case LLE -> {
        LialeImpl tmp = (LialeImpl) formula;
        Liastar operand1 = tmp.operand1;
        Liastar operand2 = tmp.operand2;
        if((operand1 instanceof LiaconstImpl) && (operand2 instanceof LiaconstImpl)) {
          long const1 = ((LiaconstImpl)operand1).value;
          long const2 = ((LiaconstImpl)operand2).value;
          return !(const1 <= const2);
        }
        break;
      }
      case LEQ -> {
        LiaeqImpl tmp = (LiaeqImpl) formula;
        Liastar operand1 = tmp.operand1;
        Liastar operand2 = tmp.operand2;
        if((operand1 instanceof LiaconstImpl) && (operand2 instanceof LiaconstImpl)) {
          long const1 = ((LiaconstImpl)operand1).value;
          long const2 = ((LiaconstImpl)operand2).value;
          return !(const1 == const2);
        }
        break;
      }
      default -> {
        return false;
      }
    }
    return false;
  }

  // return null when the conjunction is false
  // return 1 when the conjunction is true
  // Otherwise, return simplified formula
  public static Liastar simplifyConj(Liastar formula) {
    ArrayList<Liastar> literals = new ArrayList<>();
    decomposeConjunction(formula, literals);
    Liastar result = null;
    for(Liastar lit : literals) {
      if(isFalse(lit)) {
        return null;
      }
      if(lit instanceof LianotImpl) {
        LianotImpl tmp = (LianotImpl) lit;
        if(literals.contains(tmp.operand)) {
          return null;
        }
      }
      if(!isTrue(lit)) {
        result = (result == null) ? lit : mkAnd(formula.innerStar, result, lit);
      }
    }
    return (result == null) ? mkConst(formula.innerStar, 1) : result;
  }

  // return 0 = 0 when formula is true
  // return 0 = 1 when formula is false
  // Otherwise, return simplified formula
  public static Liastar simplifyDNF(Liastar formula) {
    ArrayList<Liastar> conjunctions = decomposeDNF(formula);
    Liastar result = null;
    for(Liastar conj : conjunctions) {
      Liastar simpleConj = simplifyConj(conj);
      if(simpleConj instanceof LiaconstImpl) {
        return mkEq(formula.innerStar, mkConst(formula.innerStar, 0), mkConst(formula.innerStar, 0));
      } else if(simpleConj != null) {
        result = (result == null) ? simpleConj : mkOr(formula.innerStar, result, simpleConj);
      }
    }
    return (result == null) ? mkEq(formula.innerStar, mkConst(formula.innerStar, 0), mkConst(formula.innerStar, 1)) : result;
  }

  public Liastar replaceParams(Liastar formula, HashSet<String> params, HashMap<String, String> paramInnerMap) {
    if(formula == null) {
      return formula;
    }
    switch(formula.getType()) {
      case LEQ -> {
        LiaeqImpl tmp = (LiaeqImpl) formula;
        tmp.operand1 = replaceParams(tmp.operand1, params, paramInnerMap);
        tmp.operand2 = replaceParams(tmp.operand2, params, paramInnerMap);
        return tmp;
      }
      case LLE -> {
        LialeImpl tmp = (LialeImpl) formula;
        tmp.operand1 = replaceParams(tmp.operand1, params, paramInnerMap);
        tmp.operand2 = replaceParams(tmp.operand2, params, paramInnerMap);
        return tmp;
      }
      case LLT -> {
        LialtImpl tmp = (LialtImpl) formula;
        tmp.operand1 = replaceParams(tmp.operand1, params, paramInnerMap);
        tmp.operand2 = replaceParams(tmp.operand2, params, paramInnerMap);
        return tmp;
      }
      case LOR -> {
        LiaorImpl tmp = (LiaorImpl) formula;
        tmp.operand1 = replaceParams(tmp.operand1, params, paramInnerMap);
        tmp.operand2 = replaceParams(tmp.operand2, params, paramInnerMap);
        return tmp;
      }
      case LAND -> {
        LiaandImpl tmp = (LiaandImpl) formula;
        tmp.operand1 = replaceParams(tmp.operand1, params, paramInnerMap);
        tmp.operand2 = replaceParams(tmp.operand2, params, paramInnerMap);
        return tmp;
      }
      case LITE -> {
        LiaiteImpl tmp = (LiaiteImpl) formula;
        tmp.cond = replaceParams(tmp.cond, params, paramInnerMap);
        tmp.operand1 = replaceParams(tmp.operand1, params, paramInnerMap);
        tmp.operand2 = replaceParams(tmp.operand2, params, paramInnerMap);
        return tmp;
      }
      case LNOT -> {
        LianotImpl tmp = (LianotImpl) formula;
        tmp.operand = replaceParams( tmp.operand, params, paramInnerMap);
        return tmp;
      }
      case LVAR -> {
        LiavarImpl tmp = (LiavarImpl) formula;
        if(params.contains(tmp.varName)) {
          if(paramInnerMap.containsKey(tmp.varName)) {
            return mkVar(tmp.innerStar, paramInnerMap.get(tmp.varName));
          } else {
            String newName = newVarName();
            paramInnerMap.put(tmp.varName, newName);
            return mkVar(tmp.innerStar, newName);
          }
        }
        return formula;
      }
      case LMULT -> {
        LiamultImpl tmp = (LiamultImpl) formula;
        tmp.operand1 = replaceParams(tmp.operand1, params, paramInnerMap);
        tmp.operand2 = replaceParams(tmp.operand2, params, paramInnerMap);
        return tmp;
      }
      case LPLUS -> {
        LiaplusImpl tmp = (LiaplusImpl) formula;
        tmp.operand1 = replaceParams(tmp.operand1, params, paramInnerMap);
        tmp.operand2 = replaceParams(tmp.operand2, params, paramInnerMap);
        return tmp;
      }
      default -> {
        return formula;
      }
    }
  }

  void decomposePluses(Liastar formula, HashSet<Liastar> items) {
    if(formula instanceof LiaplusImpl) {
      LiaplusImpl tmp = (LiaplusImpl) formula;
      decomposePluses(tmp.operand1, items);
      decomposePluses(tmp.operand2, items);
    } else {
      items.add(formula);
    }
  }


  void decomposeMults(Liastar formula, HashSet<Liastar> items) {
    if(formula instanceof LiamultImpl) {
      LiamultImpl tmp = (LiamultImpl) formula;
      decomposeMults(tmp.operand1, items);
      decomposeMults(tmp.operand2, items);
    } else {
      items.add(formula);
    }
  }


  // determine if formula is ite(cond, op, 0) or ite(cond, 0, op)
  // if so, return true, array[0] = cond and array[1] = op
  public static boolean ishasZeroIte(boolean isInnerStar, Liastar formula, Liastar[] array) {
    if(formula == null) {
      return false;
    }
    if(!(formula instanceof LiaiteImpl)) {
      return false;
    }
    LiaiteImpl ite = (LiaiteImpl) formula;
    if(ite.operand1.isConstV(0)) {
      array[0] = mkNot(isInnerStar, ite.cond.deepcopy());
      array[1] = ite.operand2.deepcopy();
      return true;
    } else if(ite.operand2.isConstV(0)) {
      array[0] = ite.cond.deepcopy();
      array[1] = ite.operand1.deepcopy();
      return true;
    } else {
      return false;
    }
  }

  Liastar mkConjunction(boolean innerStar, ArrayList<Liastar> conjs) {
    Liastar result = null;
    for(Liastar lit : conjs) {
      if(lit != null) {
        result = (result == null) ? lit.deepcopy() : mkAnd(innerStar, result, lit.deepcopy());
      }
    }
    if(result == null) {
      return mkEq(innerStar, mkConst(innerStar, 0), mkConst(innerStar, 0));
    } else {
      return result;
    }
  }


  public static Liastar allOuterVarEqZero(ArrayList<String> outerVector) {
    Liastar result = null;
    for(String var : outerVector) {
      Liastar tmp = mkEq(false, mkVar(false, var), mkConst(false, 0));
      result = (result == null) ? tmp : mkAnd(false, result, tmp);
    }
    return result;
  }


  public static Liastar innerVarEqOuterVar(ArrayList<String> outerVector, ArrayList<String> innerVector) {
    Liastar result = null;
    for(int i = 0; i < outerVector.size(); ++ i) {
      String outVar = outerVector.get(i);
      String inVar = innerVector.get(i);
      Liastar tmp = mkEq(false, mkVar(false, outVar), mkVar(false, inVar));
      result = (result == null) ? tmp : mkAnd(false, result, tmp);
    }
    return result;
  }


  public static Liastar expandStarWithUnderapp(Liastar formula, int m) {
    switch (formula.getType()) {
      case LCONST: case LEQ: case LNOT: case LITE: case LLT: case LLE: case LVAR: case LMULT: case LPLUS: {
        return formula;
      }
      case LOR: {
        LiaorImpl orLia = (LiaorImpl) formula;
        return mkOr(false, expandStarWithUnderapp(orLia.operand1, m), expandStarWithUnderapp(orLia.operand2, m));
      }
      case LAND: {
        LiaandImpl andLia = (LiaandImpl) formula;
        return mkAnd(false, expandStarWithUnderapp(andLia.operand1, m), expandStarWithUnderapp(andLia.operand2, m));
      }
      case LSUM: {
        LiasumImpl sumLia = (LiasumImpl) formula;
        Liastar case1 = allOuterVarEqZero(sumLia.outerVector);
        Liastar case2Part1 = innerVarEqOuterVar(sumLia.outerVector, sumLia.innerVector);
        Liastar case2Part2 = expandStarWithUnderapp(sumLia.constraints, m);
        return mkOr(false, case1, mkAnd(false, case2Part1, case2Part2));
      }
      default: {
        assert false;
        return null;
      }
    }
  }

  public static Liastar constructConjunctions(boolean innerStar, List<Liastar> formulas) {
    Liastar result = null;
    for (Liastar f : formulas) {
      if (f == null) continue;
      result = (result == null) ? f : Liastar.mkAnd(innerStar, result, f);
    }
    return result;
  }

  public static Liastar replaceVars(Liastar formula, HashMap<String, String> oldToNewVars) {
    if(formula == null) {
      return formula;
    }
    switch(formula.getType()) {
      case LEQ -> {
        LiaeqImpl tmp = (LiaeqImpl) formula;
        Liastar left = replaceVars(tmp.operand1, oldToNewVars);
        Liastar right = replaceVars(tmp.operand2, oldToNewVars);
        return Liastar.mkEq(tmp.innerStar, left, right);
      }
      case LLE -> {
        LialeImpl tmp = (LialeImpl) formula;
        Liastar left = replaceVars(tmp.operand1, oldToNewVars);
        Liastar right = replaceVars(tmp.operand2, oldToNewVars);
        return Liastar.mkLe(tmp.innerStar, left, right);
      }
      case LLT -> {
        LialtImpl tmp = (LialtImpl) formula;
        Liastar left = replaceVars(tmp.operand1, oldToNewVars);
        Liastar right = replaceVars(tmp.operand2, oldToNewVars);
        return Liastar.mkLt(tmp.innerStar, left, right);
      }
      case LOR -> {
        LiaorImpl tmp = (LiaorImpl) formula;
        Liastar left = replaceVars(tmp.operand1, oldToNewVars);
        Liastar right = replaceVars(tmp.operand2, oldToNewVars);
        return Liastar.mkOr(tmp.innerStar, left, right);
      }
      case LAND -> {
        LiaandImpl tmp = (LiaandImpl) formula;
        Liastar left = replaceVars(tmp.operand1, oldToNewVars);
        Liastar right = replaceVars(tmp.operand2, oldToNewVars);
        return Liastar.mkAnd(tmp.innerStar, left, right);
      }
      case LITE -> {
        LiaiteImpl tmp = (LiaiteImpl) formula;
        Liastar cond = replaceVars(tmp.cond, oldToNewVars);
        Liastar operand1 = replaceVars(tmp.operand1, oldToNewVars);
        Liastar operand2 = replaceVars(tmp.operand2, oldToNewVars);
        return Liastar.mkIte(tmp.innerStar, cond, operand1, operand2);
      }
      case LNOT -> {
        LianotImpl tmp = (LianotImpl) formula;
        Liastar operand = replaceVars(tmp.operand, oldToNewVars);
        return Liastar.mkNot(tmp.innerStar, operand);
      }
      case LVAR -> {
        LiavarImpl tmp = (LiavarImpl) formula;
        if(oldToNewVars.keySet().contains(tmp.varName)) {
          return mkVar(tmp.innerStar, oldToNewVars.get(tmp.varName));
        }
        return mkVar(tmp.innerStar, tmp.varName);
      }
      case LMULT -> {
        LiamultImpl tmp = (LiamultImpl) formula;
        Liastar operand1 = replaceVars(tmp.operand1, oldToNewVars);
        Liastar operand2 = replaceVars(tmp.operand2, oldToNewVars);
        return Liastar.mkMult(tmp.innerStar, operand1, operand2);
      }
      case LPLUS -> {
        LiaplusImpl tmp = (LiaplusImpl) formula;
        Liastar operand1 = replaceVars(tmp.operand1, oldToNewVars);
        Liastar operand2 = replaceVars(tmp.operand2, oldToNewVars);
        return Liastar.mkPlus(tmp.innerStar, operand1, operand2);
      }
      case LSUM -> {
        LiasumImpl sum = (LiasumImpl) formula;
        ArrayList<String> newOuterVars = new ArrayList<>();
        for (String outerVar : sum.outerVector) {
          newOuterVars.add(oldToNewVars.keySet().contains(outerVar) ? oldToNewVars.get(outerVar) : outerVar);
        }
        ArrayList<String> newInnerVars = new ArrayList<>();
        for (String innerVar : sum.innerVector) {
          newInnerVars.add(oldToNewVars.keySet().contains(innerVar) ? oldToNewVars.get(innerVar) : innerVar);
        }
        return Liastar.mkSum(formula.innerStar, newOuterVars, newInnerVars, replaceVars(sum.constraints, oldToNewVars));
      }
      default -> {
        return formula;
      }
    }
  }

  public static Liastar renameAllVars(Liastar expr, HashSet<String> exceptVars) {
    Set<String> allVars = expr.getVars();
    HashMap<String, String> oldNameToNewName = new HashMap<>();
    for (String oldName : allVars) {
      if (!exceptVars.contains(oldName) && !oldNameToNewName.containsKey(oldName)) {
        oldNameToNewName.put(oldName, newVarName());
      }
    }
    return replaceVars(expr, oldNameToNewName);
  }

  public Liastar subformulaWithoutStar() {
    return this;
  }

  /**
   * Transform the LIA* formula in post-order.
   * The method should create new instances of LIA* formulas
   * to avoid modification of their fields.
   */
  public abstract Liastar transformPostOrder(Function<Liastar, Liastar> transformer);

  @Override
  public String toString() {
    PrettyBuilder builder = new PrettyBuilder();
    //builder.setAutoNewLine(50);
    prettyPrint(builder);
    return builder.toString();
  }


  protected static void prettyPrintBinaryOp(PrettyBuilder builder,
                                            Liastar operand1, Liastar operand2,
                                            boolean needsParen1, boolean needsParen2,
                                            String op) {
    prettyPrintBinaryOp(builder, operand1, operand2,
            needsParen1, needsParen2, false, op);
  }

  protected static void prettyPrintBinaryOp(PrettyBuilder builder,
                                            Liastar operand1, Liastar operand2,
                                            boolean needsParen1, boolean needsParen2,
                                            boolean autoNewLine,
                                            String op) {
    boolean multiLine1 = operand1.isPrettyPrintMultiLine();
    boolean multiLine2 = operand2.isPrettyPrintMultiLine();
    prettyPrintBinaryOp(builder, operand1, operand2,
            needsParen1, needsParen2, multiLine1, multiLine2,
            autoNewLine, op);
  }

  /** autoNewLine: whether auto new line between operands is allowed */
  protected static void prettyPrintBinaryOp(PrettyBuilder builder,
                                     Liastar operand1, Liastar operand2,
                                     boolean needsParen1, boolean needsParen2,
                                     boolean multiLine1, boolean multiLine2,
                                     boolean autoNewLine,
                                     String op) {
    if (needsParen1) {
      if (multiLine1) {
        builder.print("(").indent(4).println();
        operand1.prettyPrint(builder);
        builder.indent(-4).println().print(")");
      } else {
        builder.print("(");
        operand1.prettyPrint(builder);
        builder.print(")");
      }
    } else
      operand1.prettyPrint(builder);

    if (multiLine1 && multiLine2) {
      builder.println().println(op);
    } else if (multiLine1) {
      builder.print(op);
    } else if (multiLine2) {
      builder.println(op);
    } else {
      builder.print(op);
    }

    // the only way to trigger auto new line
    if (autoNewLine) {
      builder.setAutoNewLineEnabled(true);
      builder.print("");
      builder.setAutoNewLineEnabled(false);
    }

    if (needsParen2) {
      if (multiLine2) {
        builder.print("(").indent(4).println();
        operand2.prettyPrint(builder);
        builder.indent(-4).println().print(")");
      } else {
        builder.print("(");
        operand2.prettyPrint(builder);
        builder.print(")");
      }
    } else
      operand2.prettyPrint(builder);
  }

  protected abstract void prettyPrint(PrettyBuilder builder);

  protected abstract boolean isPrettyPrintMultiLine();

  public static ArrayList<String> newNVarNames(int n) {
    ArrayList<String> result = new ArrayList<>();
    for (int i = 0; i < n; ++ i) {
      result.add(newVarName());
    }
    return result;
  }

  public static Liastar eqNVectors(boolean innerStar, ArrayList<String> leftVector, ArrayList<ArrayList<String>> rightVectors) {
    Liastar result = null;
    for (int i = 0; i < leftVector.size(); ++ i) {
      LiavarImpl leftVar = (LiavarImpl) mkVar(innerStar, leftVector.get(i));
      Liastar rightPlusFormula = null;
      for (int j = 0; j < rightVectors.size(); ++ j) {
        LiavarImpl rightVar = (LiavarImpl) mkVar(innerStar, rightVectors.get(j).get(i));
        rightPlusFormula = (rightPlusFormula == null) ? rightVar : mkPlus(innerStar, rightPlusFormula, rightVar);
      }
      Liastar leftEqRight = mkEq(innerStar, leftVar, rightPlusFormula);
      result = (result == null) ? leftEqRight : mkAnd(innerStar, result, leftEqRight);
    }
    return result;
  }

  public static Liastar calculateUnderApprox(Liastar formula, int n) {
    Liastar result = spanLiastarByNVectors(formula, n);
    return expandStarWithUnderapp(result, 1);
  }

  public static Liastar spanLiastarByNVectors(Liastar formula, int n) {
    switch (formula.getType()) {
      case LPLUS: case LMULT: case LVAR: case LLT: case LLE: case LEQ: case LDIV: case LCONST: case LSTRING: case LFUNC: {
        return formula;
      }
      case LOR: {
        LiaorImpl orFormula = (LiaorImpl) formula;
        orFormula.operand1 = spanLiastarByNVectors(orFormula.operand1, n);
        orFormula.operand2 = spanLiastarByNVectors(orFormula.operand2, n);
        return orFormula;
      }
      case LAND: {
        LiaandImpl andFormula = (LiaandImpl) formula;
        andFormula.operand1 = spanLiastarByNVectors(andFormula.operand1, n);
        andFormula.operand2 = spanLiastarByNVectors(andFormula.operand2, n);
        return andFormula;
      }
      case LITE: {
        LiaiteImpl iteFormula = (LiaiteImpl) formula;
        iteFormula.cond = spanLiastarByNVectors(iteFormula.cond, n);
        return iteFormula;
      }
      case LNOT: {
        LianotImpl notFormula = (LianotImpl) formula;
        notFormula.operand = spanLiastarByNVectors(notFormula.operand, n);
        return notFormula;
      }
      case LSUM: {
        LiasumImpl sumFormula = (LiasumImpl) formula;
        ArrayList<ArrayList<String>> newNameVectors = new ArrayList<>();
        for (int i = 0; i < n; ++ i) {
          newNameVectors.add(newNVarNames(sumFormula.outerVector.size()));
        }
        Liastar outerEqSumOfNVectors = eqNVectors(sumFormula.innerStar, sumFormula.outerVector, newNameVectors);
        Liastar newLiasumFormulas = null;
        for (int i = 0; i < n; ++ i) {
          ArrayList<String> newOuterNames = newNameVectors.get(i);
          LiasumImpl tmpSumFormula = (LiasumImpl) sumFormula.deepcopy();
          tmpSumFormula.outerVector = newOuterNames;
          tmpSumFormula = (LiasumImpl) renameAllInnerVars(tmpSumFormula);
          tmpSumFormula.constraints = spanLiastarByNVectors(tmpSumFormula.constraints, n);
          newLiasumFormulas = (newLiasumFormulas == null) ? tmpSumFormula : mkAnd(sumFormula.innerStar, newLiasumFormulas, tmpSumFormula);
        }
        Liastar result = mkAnd(sumFormula.innerStar, outerEqSumOfNVectors, newLiasumFormulas);
        return result;
      }
      default: {
        assert false;
        System.err.println("not support liaterm");
        return null;
      }
    }
  }

  public static Liastar renameAllInnerVars(Liastar formula) {
    switch (formula.getType()) {
      case LFUNC: case LSTRING: case LCONST: case LDIV: case LEQ: case LLE: case LLT: case LVAR: case LMULT: case LPLUS: {
         return formula;
      }
      case LOR: {
        LiaorImpl orFormula = (LiaorImpl) formula;
        orFormula.operand1 = renameAllInnerVars(orFormula.operand1);
        orFormula.operand2 = renameAllInnerVars(orFormula.operand2);
        return orFormula;
      }
      case LAND: {
        LiaandImpl andFormula = (LiaandImpl) formula;
        andFormula.operand1 = renameAllInnerVars(andFormula.operand1);
        andFormula.operand2 = renameAllInnerVars(andFormula.operand2);
        return andFormula;
      }
      case LITE: {
        LiaiteImpl iteFormula = (LiaiteImpl) formula;
        iteFormula.cond = renameAllInnerVars(iteFormula.cond);
        return iteFormula;
      }
      case LNOT: {
        LianotImpl notFormula = (LianotImpl) formula;
        notFormula.operand = renameAllInnerVars(notFormula.operand);
        return notFormula;
      }
      case LSUM: {
        LiasumImpl sumFormula = (LiasumImpl) formula;
        HashMap<String, String> renameMapping = new HashMap<>();
        for (String innerVarName : sumFormula.innerVector) {
          renameMapping.put(innerVarName, newVarName());
        }
        sumFormula = (LiasumImpl) replaceVars(sumFormula, renameMapping);
        sumFormula.constraints = renameAllInnerVars(sumFormula.constraints);
        return sumFormula;
      }
      default: {
        assert false;
        System.err.println("not support liaterm");
        return null;
      }
    }
  }

}

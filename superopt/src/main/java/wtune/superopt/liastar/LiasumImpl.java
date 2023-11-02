package wtune.superopt.liastar;

import com.microsoft.z3.*;
import wtune.superopt.logic.LogicSupport;
import wtune.superopt.logic.SqlSolver;
import wtune.superopt.util.PrettyBuilder;

import java.util.*;
import java.util.function.Function;

import static wtune.common.utils.IterableSupport.all;import static wtune.common.utils.IterableSupport.any;


public class LiasumImpl extends Liastar {

  ArrayList<String> outerVector;
  ArrayList<String> innerVector;
  Liastar constraints;

  LiasumImpl() {
    outerVector = new ArrayList<>();
    innerVector = new ArrayList<>();
    constraints = null;
  }

  @Override
  public Liastar mergeMult(HashMap<LiamultImpl, String> multToVar) {
    HashMap<LiamultImpl, String> curMap = new HashMap<>();
    constraints = constraints.mergeMult(curMap);
    for(LiamultImpl l : curMap.keySet()) {
      Liastar result = (LiavarImpl) mkVar(true, curMap.get(l));
      Set<String> vars = l.collectVarSet();
      for(String v : vars) {
        Liastar cur = (LiavarImpl) mkVar(true, v);
        Liastar newconstr = mkEq(true, cur, mkConst(true, 0));
        newconstr = mkNot(true, newconstr);
        newconstr = mkOr(true, newconstr,
            mkEq(true, result, mkConst(true, 0)));
        constraints = mkAnd(true, constraints, newconstr);
      }

      // (v1 !=0 /\ ... /\ vn !=0) -> (v != 0)
      Liastar eqzeroConstr = null;
      for(String v : vars) {
        Liastar cur = (LiavarImpl) mkVar(true, v);
        Liastar newconstr = mkEq(true, cur, mkConst(true, 0));
        eqzeroConstr = (eqzeroConstr == null) ? newconstr : mkOr(true, eqzeroConstr, newconstr);
      }
      Liastar resultNotzero = mkNot(true, mkEq(true, result, mkConst(true, 0)));
      constraints = mkAnd(true, constraints, mkOr(true, eqzeroConstr, resultNotzero) );
    }
    updateInnerVector();

    return this;
  }

  LiasumImpl(ArrayList<String> v1, ArrayList<String> v2, Liastar c) {
    outerVector = v1;
    innerVector = v2;
    constraints = c;
  }

  @Override
  public LiaOpType getType() {
    return LiaOpType.LSUM;
  }

  @Override
  public boolean isLia() {
    return false;
  }

  @Override
  protected void prettyPrint(PrettyBuilder builder) {
    builder.print("(");
    for (int i = 0, bound = outerVector.size(); i < bound; i++) {
      builder.print(outerVector.get(i));
      if (i < bound - 1) builder.print(", ");
    }
    builder.println(") ∈");
    builder.print("{(");
    for (int i = 0, bound = innerVector.size(); i < bound; i++) {
      builder.print(innerVector.get(i));
      if (i < bound - 1) builder.print(", ");
    }
    builder.print(") | ");
    builder.indent(4).println();
    constraints.prettyPrint(builder);
    builder.indent(-4).println();
    builder.print("}*");
  }

  @Override
  protected boolean isPrettyPrintMultiLine() {
    return true;
  }

  @Override
  public Set<String> getVars() {
    HashSet<String> result = new HashSet<>(constraints.getVars());
    result.addAll(outerVector);
    return result;
  }

  @Override
  public Liastar deepcopy() {
    ArrayList<String> v1 = new ArrayList<>();
    v1.addAll(outerVector);

    ArrayList<String> v2 = new ArrayList<>();
    v2.addAll(innerVector);

    return mkSum(innerStar, v1, v2, constraints.deepcopy());
  }

  @Override
  public Set<String> collectVarSet() {
    return new HashSet<>(outerVector);
  }
  
  @Override
  public Liastar multToBin(int n) {
    Set<String> varSet = constraints.collectVarSet();
    int upperBound = 1 << n - 1;
    for(String v : varSet) {
      Liastar boundCond = mkLe(true, mkVar(true, v), mkConst(true, upperBound));
      constraints = mkAnd(true, constraints, boundCond);
    }
    constraints = constraints.multToBin(n);
    return this;
//    Set<String> varSet = constraints.collectVarSet();
//    Liastar varToBin = null;
//    for(String v : varSet) {
//        Liastar tmp = mkIte( true,
//            mkEq(true, mkVar(true, v + "_0"), mkConst(true,0)),
//            mkConst(true, 0),
//            mkConst(true,1)
//        );
//        for(int i = 1; i < n; ++ i) {
//          tmp = mkPlus(true, tmp,
//                mkIte(true,
//                    mkEq(true, mkVar(true,v + "_" + i), mkConst(true,0)),
//                    mkConst(true, 0),
//                    mkConst(true, 1 << i)
//                )
//              );
//        }
//
//        if(varToBin == null) {
//          varToBin = mkEq(true, mkVar(true, v), tmp);
//        } else {
//          varToBin = mkAnd(true,
//              varToBin,
//              mkEq(true, mkVar(true, v), tmp)
//          );
//        }
//
//      for(int i = 0; i < n; ++ i) {
//        varToBin = mkAnd(true,
//            varToBin,
//            mkLe(true, mkVar(true, v + "_" + i), mkConst(true, 1))
//        );
//        varToBin = mkAnd(true,
//            varToBin,
//            mkLe(true, mkConst(true, 0), mkVar(true, v + "_" + i))
//        );
//      }
//    }
//
//    constraints = mkAnd(true, constraints, varToBin);
//    constraints = constraints.multToBin(n);
//
//    return this;
  }

  @Override
  public Liastar simplifyMult(HashMap<Liastar, String> multToVar) {
    constraints.innerStar = true;

    Liastar tmp = constraints.simplifyMult(multToVar);
    if(tmp != null)
      constraints = mkAnd(true, constraints, tmp);

    return null;
  }

  public void updateInnerVector() {
    Set<String> varSet = constraints.collectVarSet();
    int innerVarNum = innerVector.size();
    for(String s : varSet) {
      int i = 0;
      for( ; i < innerVarNum; ++ i) {
        if(innerVector.get(i).equals(s))
          break;
      }
      if(i == innerVarNum)
        innerVector.add(s);
    }
  }

  SemiLinearSet getsls() throws Exception {
    int i = 0;
    SemiLinearSet sls = new SemiLinearSet();
    boolean flag = sls.augment(innerVector, constraints, outerVector.size());
    while(flag == true && i < 1000) {
//      sls.saturate(innerVector, constraints);
      flag = sls.augment(innerVector, constraints, outerVector.size());
      i = i + 1;
    }
    if (i == 1000) {
      throw new Exception("too much sls");
    }
    return sls;
  }

  @Override
  public Liastar expandStar() throws Exception {
    constraints = constraints.expandStar();
    updateInnerVector();
    try {
      SemiLinearSet sls = getsls();
      return sls.tranToLiastar(outerVector);
    } catch (Exception e) {
      if (LogicSupport.dumpLiaFormulas) {
        System.out.println(e);
      }
      return nativeExpandstar();
    }
  }

//  static void findExpForVar(Liastar formula, HashMap<String, Liastar> expOfVars) {
//    switch(formula.getType()) {
//      case LAND -> {
//        LiaandImpl andLia = (LiaandImpl) formula;
//        findExpForVar(andLia.operand1, expOfVars);
//        findExpForVar(andLia.operand2, expOfVars);
//      }
//      case LEQ -> {
//        LiaeqImpl eqLia = (LiaeqImpl) formula;
//        if(eqLia.operand1 instanceof LiavarImpl) {
//          expOfVars.put(((LiavarImpl) eqLia.operand1).varName, eqLia.operand2);
//        }
//      }
//      default -> {
//        return;
//      }
//    }
//  }

//  Liastar nativeExpandstar() {
//    Liastar result = null;
//    HashMap<String, Liastar> expOfVars = new HashMap<>();
//    findExpForVar(constraints, expOfVars);
//    for(int i = 0; i < outerVector.size(); ++ i) {
//      String outVar1 = outerVector.get(i);
//      String inVar1 = innerVector.get(i);
//      Liastar inVar1Value = expOfVars.get(inVar1);
//      if(inVar1Value == null) continue;
//      for(int j = i + 1; j < outerVector.size(); ++ j) {
//        String outVar2 = outerVector.get(j);
//        String inVar2 = innerVector.get(j);
//        Liastar inVar2Value = expOfVars.get(inVar2);
//        if(inVar2Value != null) {
//          if (inVar1Value.equals(inVar2Value)){
//            Liastar newExp = mkEq(false, mkVar(false, outVar1), mkVar(false, outVar2));
//            result = (result == null) ? newExp : mkAnd(false, result, newExp);
//          }
//        }
//      }
//    }
//    if(result == null) {
//      return mkEq(false, mkConst(false, 0), mkConst(false, 0));
//    } else {
//      return result;
//    }
//  }

  @Override
  public Expr transToSMT(Context ctx, HashMap<String, IntExpr> varsName) {
    System.err.println("there should not be star");
    assert false;
    return null;
  }

  @Override
  public EstimateResult estimate() {
    EstimateResult r = constraints.estimate();
    int rn = r.vars.size() + r.n_extra;
    int d = innerVector.size();
    int n = (int)Math.ceil(6 * d * (Math.log(4 * d) / Math.log(2) + 2 * r.m * Math.log(2 + (rn + 1) * r.a) / Math.log(2)));
    double a = Math.pow(2 + (rn + 1) * r.a, 2 * r.m);
    return new EstimateResult(
            new HashSet(outerVector),
            n,
            d,
            a
    );
  }

  @Override
  public Expr expandStarWithK(Context ctx, Solver sol, String suffix) {
    EstimateResult r = constraints.estimate();
    int d = innerVector.size(), n = r.vars.size() + r.n_extra, m = r.m;
    double a = r.a;
    int k = (int)Math.ceil(4 * d * (Math.log(4 * d) / Math.log(2) + 2 * m * Math.log(2 + (n + 1) * a)) / Math.log(2));
    if (suffix.matches("(\\_1)*")) {
      //System.out.printf("expanding star for %s; suffix '%s'...\n", this.toString(), suffix);
      //System.out.printf("expanding star: n = %d, m = %d, a = %f; k = %d\n", n, m, a, k);
    }

    int l = outerVector.size();
    ArithExpr[] sum_vec = new ArithExpr[l];
    for (int i = 0; i < l; i++) sum_vec[i] = ctx.mkInt(0);

    for (int i = 1; i <= k; i++) {
      String suf = String.format("%s_%d", suffix, i);
      for (String var : r.vars) {
        sol.add(ctx.mkGe(
                ctx.mkIntConst(var + suf),
                ctx.mkInt(0)
        ));
      }
      for (int j = 0; j < l; j++) {
        sol.add(ctx.mkGe(
                ctx.mkIntConst(innerVector.get(j) + suf),
                ctx.mkInt(0)
        ));
        sum_vec[j] = ctx.mkAdd(sum_vec[j], ctx.mkIntConst(innerVector.get(j) + suf));
      }
      sol.add((BoolExpr)constraints.expandStarWithK(ctx, sol, suf));
    }

    BoolExpr e = ctx.mkTrue();
    for (int i = 0; i < l; i++)
      e = ctx.mkAnd(e, ctx.mkEq(ctx.mkIntConst(outerVector.get(i) + suffix), sum_vec[i]));
    return e;
  }

  @Override
  public boolean equals(Object that) {
    if(that == this)
      return true;
    if(that == null)
      return false;
    if(!(that instanceof LiasumImpl))
      return false;
    LiasumImpl tmp = (LiasumImpl) that;
    return outerVector.equals(tmp.outerVector) && innerVector.equals(tmp.innerVector) && constraints.equals(tmp.constraints);
  }

  @Override
  public int hashCode() {
    return constraints.hashCode();
  }

  @Override
  public void prepareInnervector(HashSet<String> vars) {
    updateInnerVector();
    ArrayList<String> tmp = new ArrayList<>(innerVector);
    for(String v : tmp) {
      if(vars.contains(v)) {
        innerVector.remove(v);
      }
    }
    vars.addAll(innerVector);
    constraints.prepareInnervector(vars);
    return;
  }

  HashSet<String> getImportantInnerVars() {
    HashSet<String> result = new HashSet<>();
    for(int i = 0; i < outerVector.size(); ++ i)
      result.add(innerVector.get(i));
    return result;
  }

  boolean classifyConjunction(
      Liastar formula,
      HashSet<String> params,
      HashSet<String> varsWithoutParam,
      ArrayList<Liastar> conjWithoutParam,
      HashSet<String> varsWithParam,
      ArrayList<Liastar> conjWithParam
  ) {

    HashSet<String> varsWithoutParam2 = new HashSet<>();
    ArrayList<Liastar> conjWithoutParam2 = new ArrayList<>();
    HashSet<String> varsWithParam2 = new HashSet<>();
    ArrayList<Liastar> conjWithParam2 = new ArrayList<>();

    boolean b = classifyConjunction2(false, formula, params, varsWithoutParam2, conjWithoutParam2, varsWithParam2, conjWithParam2);
    if(b == false) {
      return classifyConjunction2(true, formula, params, varsWithoutParam, conjWithoutParam, varsWithParam, conjWithParam);
    } else {
      varsWithoutParam.addAll(varsWithoutParam2);
      conjWithoutParam.addAll(conjWithoutParam2);
      varsWithParam.addAll(varsWithParam2);
      conjWithParam.addAll(conjWithParam2);
      return true;
    }

  }

  boolean classifyConjunction2(
      boolean flag,
      Liastar formula,
      HashSet<String> params,
      HashSet<String> varsWithoutParam,
      ArrayList<Liastar> conjWithoutParam,
      HashSet<String> varsWithParam,
      ArrayList<Liastar> conjWithParam
  ) {
    HashSet<String> importantInnerVar = getImportantInnerVars();
    ArrayList<Liastar> literals = new ArrayList<>();
    decomposeConjunction(formula, literals);
    Liastar formulaWithoutParams = null;
    Liastar formulaWithParams = null;
    for(Liastar lit : literals) {
      Set<String> vars = lit.collectVarSet();
      if(overLap(vars, params) || (flag && !overLap(vars, importantInnerVar))) {
        if(overLap(vars, varsWithoutParam)) {
          return false;
        } else {
          varsWithParam.addAll(vars);
          formulaWithParams = (formulaWithParams == null) ? lit : mkAnd(innerStar, formulaWithParams, lit);
        }
      } else {
        if(overLap(vars, varsWithParam)) {
          return false;
        } else {
          varsWithoutParam.addAll(vars);
          formulaWithoutParams = (formulaWithoutParams == null) ? lit : mkAnd(innerStar, formulaWithoutParams, lit);
        }
      }
    }

    conjWithParam.add(formulaWithParams);
    conjWithoutParam.add(formulaWithoutParams);
    return true;
  }

  boolean classifyConjunctions(
      Liastar formula,
      HashSet<String> params,
      HashSet<String> varsWithoutParam,
      ArrayList<Liastar> conjWithoutParam,
      HashSet<String> varsWithParam,
      ArrayList<Liastar> conjWithParam
  ) {
    ArrayList<Liastar> conjunctions = decomposeDNF(formula);
    for(Liastar conj : conjunctions) {
      if(!classifyConjunction(conj, params, varsWithoutParam, conjWithoutParam, varsWithParam, conjWithParam)) {
        return false;
      }
    }
    for(int i = 0; i < outerVector.size(); ++ i) {
      if(varsWithParam.contains(innerVector.get(i))) {
        return false;
      }
    }
    return true;
  }

  Liastar buildLinearCombLia(ArrayList<String> result, ArrayList<ArrayList<String>> vectors) {
    Liastar formula = null;
    for(int i = 0; i < result.size(); ++ i) {
      Liastar sum = null;
      for(int j = 0; j < vectors.size(); ++ j) {
        Liastar var = mkVar(innerStar, vectors.get(j).get(i));
        sum = (sum == null) ? var : mkPlus(innerStar, sum, var);
      }
      Liastar equation = mkEq(innerStar, mkVar(innerStar, result.get(i)), sum);
      formula = (formula == null) ? equation : mkAnd(innerStar, formula, equation);
    }
    assert (formula != null);
    return formula;
  }

  Liastar zeroVectorLia(ArrayList<String> vector) {
    Liastar result = null;
    for(String var : vector) {
      Liastar tmp = mkEq(innerStar, mkVar(innerStar, var), mkConst(innerStar, 0));
      result = (result == null) ? tmp : mkAnd(innerStar, result, tmp);
    }
    return result;
  }

  Liastar buildOneVectorLia(
      ArrayList<String> xs,
      HashSet<String> ys,
      Liastar conjWithoutParam,
      Liastar conjWithParam
  ) {
    Liastar right = zeroVectorLia(xs);

    ArrayList<String> curOuterVector = new ArrayList<>(xs);
    ArrayList<String> curInnerVector = new ArrayList<>(innerVector);
    Liastar curConstraint = conjWithoutParam.deepcopy();
    curConstraint.innerStar = innerStar;
    LiasumImpl star = (LiasumImpl) mkSum(innerStar, curOuterVector, curInnerVector, curConstraint);
    star.updateInnerVector();

    Liastar paramLia = replaceParams(conjWithParam, ys, new HashMap<>());

    Liastar left = mkAnd(innerStar, star, paramLia);

    return mkOr(innerStar, left, right);
  }

  HashSet<String> buildYs(HashSet<String> varsWithParams, HashSet<String> params) {
    HashSet<String> result = new HashSet<>();
    for(String var : varsWithParams) {
      if(!params.contains(var)) {
        result.add(var);
      }
    }
    return result;
  }

  Liastar buildVectorsLia(
      ArrayList<ArrayList<String>> newVectors,
      HashSet<String> ys,
      ArrayList<Liastar> conjsWithoutParam,
      ArrayList<Liastar> conjsWithParam
  ) {
    Liastar result = null;
    for(int i = 0; i < newVectors.size(); ++ i) {
      ArrayList<String> vector = newVectors.get(i);
      Liastar conjWithutParam = conjsWithoutParam.get(i);
      Liastar conjWithParam = conjsWithParam.get(i);
      Liastar tmp = buildOneVectorLia(vector, ys, conjWithutParam, conjWithParam);
      result = (result == null) ? tmp : mkAnd(innerStar, result, tmp);
    }
    return result;
  }

  Liastar moveoutParams(
      HashSet<String> ys,
      ArrayList<Liastar> conjWithoutParam,
      ArrayList<Liastar> conjWithParam
  ) {
    ArrayList<ArrayList<String>> newVectors = new ArrayList<>();
    for(int i = 0; i < conjWithParam.size(); ++ i) {
      ArrayList<String> newVector = new ArrayList<>();
      newVectors.add(newVector);
      for (int j = 0; j < outerVector.size(); ++j) {
        newVector.add(newVarName());
      }
    }
    Liastar result = buildLinearCombLia(outerVector, newVectors);

    result = mkAnd(innerStar, result, buildVectorsLia(newVectors, ys, conjWithoutParam, conjWithParam));
    return result;
  }

  @Override
  public HashSet<String> collectParams() {
    HashSet<String> params = constraints.collectParams();
    for(String var : innerVector) {
      if(params.contains(var)) {
        params.remove(var);
      }
    }
    Set<String> allVars = constraints.collectVarSet();
    for(String v : allVars) {
      if(!innerVector.contains(v)) {
        params.add(v);
      }
    }
    return params;
  }

  static ArrayList<String[]> newOuterVarNames(int numOfVectos, int numOfNames) {
    ArrayList<String[]> newOuterVars = new ArrayList<>();
    for (int i = 0; i < numOfVectos; ++ i) {
      String[] names = new String[numOfNames];
      for (int j = 0; j < numOfNames; ++ j)
        names[j] = Liastar.newVarName();
      newOuterVars.add(names);
    }
    return newOuterVars;
  }

  Liastar eqVectorsSum(ArrayList<String> left, ArrayList<String[]> rights) {
    ArrayList<Liastar> formulas = new ArrayList<>();
    for (String leftVar : left) {
      Liastar tmp = null;
      LiavarImpl leftLVar = (LiavarImpl) Liastar.mkVar(innerStar, leftVar);
      for (String[] rightVars : rights) {
        LiavarImpl rightLVar = (LiavarImpl) Liastar.mkVar(innerStar, rightVars[0]);
        tmp = (tmp == null) ? rightLVar : Liastar.mkPlus(innerStar, tmp, rightLVar);
      }
      tmp = Liastar.mkEq(innerStar, leftLVar, tmp);
      formulas.add(tmp);
    }
    return constructConjunctions(innerStar, formulas);
  }

  private static ArrayList<String> firstNElements(int n, ArrayList<String> innerVector) {
    assert innerVector.size() >= n;
    ArrayList<String> result = new ArrayList<>();
    for(int i = 0; i < n; ++ i)
      result.add(innerVector.get(i));
    return result;
  }

  private static Liastar removeParamsFromConjunction(
      boolean innerStar, String[] outerVector, ArrayList<String> innerVector, Liastar conjunction, HashSet<String> params) {

    ArrayList<Liastar> literals = new ArrayList<>();
    decomposeConjunction(conjunction, literals);
    HashSet<String> varsOutStar = new HashSet<>(params);
    HashSet<String> varsUnderStar = new HashSet<>(innerVector);
    ArrayList<String> varsMustUnderStar = firstNElements(outerVector.length, innerVector);
    ArrayList<Liastar> literalsOutStar = new ArrayList<>();
    ArrayList<Liastar> literalsUnderStar = literals;
    boolean modified = false;
    do {
      modified = false;
      ArrayList<Liastar> movedLiterals = new ArrayList<>();
      HashSet<String> movedVars = new HashSet<>();
      for (Liastar l : literalsUnderStar) {
        Set<String> varSet = l.collectVarSet();
        if (any(varSet, s -> varsOutStar.contains(s))) {
          movedLiterals.add(l);
          movedVars.addAll(varSet);
          modified = true;
        }
      }
      if (!movedLiterals.isEmpty()) {
        literalsUnderStar.removeAll(movedLiterals);
        varsUnderStar.removeAll(movedVars);
        literalsOutStar.addAll(movedLiterals);
        varsOutStar.addAll(movedVars);
        if (any(varsOutStar, v -> varsMustUnderStar.contains(v)))
          return null;
      }
    } while (modified == true);

    ArrayList<String> newOuterVars = new ArrayList();
    newOuterVars.addAll(Arrays.stream(outerVector).toList());
    Liastar newConstraints = constructConjunctions(innerStar, literalsUnderStar);
    ArrayList<String> newInnerVars = new ArrayList(varsMustUnderStar);
    for (String v : newConstraints.collectVarSet()) {
      if (!newInnerVars.contains(v))
        newInnerVars.add(v);
    }
    Liastar sum = Liastar.mkSum(innerStar, newOuterVars, newInnerVars, newConstraints);

    Liastar eqzero = allOuterVarEqZero(newOuterVars);
    Liastar existsProp = constructConjunctions(innerStar, literalsOutStar);
    Liastar result = (literalsOutStar.isEmpty()) ? Liastar.mkAnd(innerStar, sum, existsProp) :
        Liastar.mkOr(innerStar, eqzero, Liastar.mkAnd(innerStar, sum, existsProp));

    HashSet<String> exceptVars = new HashSet<>();
    exceptVars.addAll(params);
    exceptVars.addAll(List.of(outerVector));
    result = renameAllVars(result, exceptVars);

    return result;
  }


  private Liastar removeParamsFromConjunctions(ArrayList<Liastar> conjunctions, HashSet<String> params) {
    if (conjunctions.isEmpty())
      return null;

    ArrayList<String[]> newOuterVectors = newOuterVarNames(conjunctions.size(), outerVector.size());
    Liastar eqFormula = eqVectorsSum(outerVector, newOuterVectors);

    ArrayList<Liastar> results = new ArrayList<>();
    results.add(eqFormula);
    for (int i = 0; i < conjunctions.size(); ++ i) {
      String[] newOuterVector = newOuterVectors.get(i);
      Liastar tmp = removeParamsFromConjunction(innerStar, newOuterVector, innerVector, conjunctions.get(i), params);
      if (tmp == null) {
        return null;
      } else {
        results.add(tmp);
      }
    }
    return constructConjunctions(innerStar, results);
  }


  @Override
  public Liastar removeParameter() {
    HashSet<String> params = collectParams();
    if (LogicSupport.dumpLiaFormulas)
      System.out.println("remove param for" + constraints);
    constraints = constraints.removeParameter();
    Set<String> vars = constraints.collectVarSet();
    for(String var : vars) {
      if(!params.contains(var) && !innerVector.contains(var)) {
        innerVector.add(var);
      }
    }
    if(params.isEmpty()) {
      return this;
    }

    if (LogicSupport.dumpLiaFormulas)
      System.out.println("dnf for" + constraints);

//    if(constraints.collectVarSet().size() > 4) {
//      constraints = replaceParams(constraints, params, new HashMap<>());
//      updateInnerVector();
//      return this;
//    }

    try {
      setDnfStartTime();
      Liastar tmpConst = constraints.deepcopy();
      tmpConst = paramLiaStar2DNF(tmpConst, true);
      if (LogicSupport.dumpLiaFormulas)
        System.out.println("dnf is" + tmpConst);
      ArrayList<Liastar> conjunctions = decomposeDNF(tmpConst);
      tmpConst = simplifyDNF(tmpConst);

      HashSet<String> varsWithParam = new HashSet<>();
      HashSet<String> varsWithoutParam = new HashSet<>();
      ArrayList<Liastar> conjWithParam = new ArrayList<>();
      ArrayList<Liastar> conjWithoutParam = new ArrayList<>();
      boolean canSolve = classifyConjunctions(tmpConst, params, varsWithoutParam, conjWithoutParam, varsWithParam, conjWithParam);
      if (canSolve == true) {
        return moveoutParams(buildYs(varsWithParam, params), conjWithoutParam, conjWithParam);
      } else {
        if (LogicSupport.dumpLiaFormulas)
          System.err.println("dnf fails");
        constraints = replaceParams(constraints, params, new HashMap<>());
        updateInnerVector();
        return this;
      }

    } catch (Exception e) {
      if (LogicSupport.dumpLiaFormulas)
        System.err.println("dnf is timeout");
      constraints = replaceParams(constraints, params, new HashMap<>());
      updateInnerVector();
      return this;
    }
  }


  @Override
  public Liastar removeParameterEager() {
    HashSet<String> params = collectParams();
    if (LogicSupport.dumpLiaFormulas)
      System.out.println("eager remove param for" + constraints);
    constraints = constraints.removeParameterEager();
    Set<String> vars = constraints.collectVarSet();
    for(String var : vars) {
      if(!params.contains(var) && !innerVector.contains(var)) {
        innerVector.add(var);
      }
    }
    if(params.isEmpty()) {
      return this;
    }

    if (LogicSupport.dumpLiaFormulas)
      System.out.println("eager dnf for" + constraints);

    try {
      setDnfStartTime();
      Liastar tmpConst = constraints.deepcopy();
      tmpConst = paramLiaStar2DNF(tmpConst, true);
      if (LogicSupport.dumpLiaFormulas)
        System.out.println("eager dnf is" + tmpConst);
      ArrayList<Liastar> conjunctions = decomposeDNF(tmpConst);
      tmpConst = simplifyDNF(tmpConst);

      Liastar result = removeParamsFromConjunctions(decomposeDNF(tmpConst), params);
      if (result != null) {
        return result;
      } else {
        if (LogicSupport.dumpLiaFormulas)
          System.err.println("eager dnf fails");
        constraints = replaceParams(constraints, params, new HashMap<>());
        updateInnerVector();
        return this;
      }

    } catch (Exception e) {
      if (LogicSupport.dumpLiaFormulas)
        System.err.println("eager dnf is timeout");
      constraints = replaceParams(constraints, params, new HashMap<>());
      updateInnerVector();
      return this;
    }
  }


  @Override
  public Liastar simplifyIte() {
    constraints = constraints.simplifyIte();
    return this;
  }

  @Override
  public Liastar pushUpParameter(HashSet<String> newVars) {
    HashSet<String> newInnerVars = new HashSet<>();
    constraints.pushUpParameter(newInnerVars);
    for(String var : newInnerVars) {
      innerVector.add(var);
    }
    mergeParameterIte();

    Liastar newFormula = this;
    for(int i = 0; i < outerVector.size(); ++ i) {
      Liastar tmp = pushUpParameterForOneOutVar(i, newVars, constraints);
      if(tmp != null) {
        newFormula = mkAnd(innerStar, newFormula, tmp.deepcopy());
      }
    }

    return newFormula.deepcopy();
  }

  Liastar pushUpParameterForOneOutVar(int index, HashSet<String> newVars, Liastar formula) {
    switch (formula.getType()) {
      case LAND: {
        Liastar tmp = pushUpParameterForOneOutVar(index, newVars, ((LiaandImpl)formula).operand1);
        if (tmp != null) {
          return tmp;
        } else {
          return pushUpParameterForOneOutVar(index, newVars, ((LiaandImpl)formula).operand2);
        }
      }
      case LEQ: {
        String innerVar = innerVector.get(index);
        Liastar left = ((LiaeqImpl) formula).operand1;
        Liastar right = ((LiaeqImpl) formula).operand2;
        if(left instanceof LiavarImpl && right instanceof LiaiteImpl) {
          LiavarImpl leftVar = (LiavarImpl) left;
          if(!leftVar.varName.equals(innerVar)) {
            return null;
          }
          LiaiteImpl rightIte = (LiaiteImpl) right;
          if(!(rightIte.operand2 instanceof LiaconstImpl)) {
            return null;
          }
          if( ((LiaconstImpl)rightIte.operand2).value != 0 ) {
            return null;
          }




          Liastar paramMult = null;
          if (rightIte.operand1 instanceof LiamultImpl) {
            HashSet<Liastar> items = new HashSet<>();
            decomposeMults((LiamultImpl) rightIte.operand1, items);
            Liastar innerMult = null;
            for (Liastar op2 : items) {
              if (op2 instanceof LiavarImpl && !innerVector.contains(op2.toString())) {
                paramMult = (paramMult == null) ? op2.deepcopy() : mkMult(true, paramMult, op2.deepcopy());
              } else {
                innerMult = (innerMult == null) ? op2.deepcopy() : mkMult(true, innerMult, op2.deepcopy());
              }
            }
            rightIte.operand1 = (innerMult == null) ? mkConst(true, 1) : innerMult;
          }




          Liastar[] conds = new Liastar[2];
          conds[0] = null;
          conds[1] = null;
          decomposeConditions(rightIte.cond, conds);
          if(conds[1] == null) {
            return null;
          } else {
            if (conds[0] != null) {
              rightIte.cond = conds[0].deepcopy();
            } else {
              ((LiaeqImpl) formula).operand2 = rightIte.operand1;
            }
            String newOutVar = newVarName();
            newVars.add(newOutVar);
            String oldOutVar = outerVector.get(index);
            outerVector.set(index, newOutVar);
            if (paramMult == null)
              return mkEq(innerStar,
                  mkVar(innerStar, oldOutVar),
                  mkIte(innerStar, conds[1].deepcopy(), mkVar(innerStar, newOutVar), mkConst(innerStar, 0))
              );
            else
              return mkEq(innerStar,
                  mkVar(innerStar, oldOutVar),
                  mkIte(innerStar, conds[1].deepcopy(), mkMult(innerStar, paramMult, mkVar(innerStar, newOutVar)), mkConst(innerStar, 0))
              );
          }
        }
      }
      default: {
        return null;
      }
    }
  }

  void decomposeConditions(Liastar cond, Liastar[] condArray) {
    if (cond instanceof LiaandImpl) {
      decomposeConditions(((LiaandImpl)cond).operand1, condArray);
      decomposeConditions(((LiaandImpl)cond).operand2, condArray);
    } else {
      Set<String> vars = cond.collectVarSet();
      for(String var : vars) {
        if (innerVector.contains(var)) {
          condArray[0] = (condArray[0] == null) ? cond : mkAnd(innerStar, condArray[0], cond);
          return;
        }
      }
      condArray[1] = (condArray[1] == null) ? cond : mkAnd(innerStar, condArray[1], cond);
    }
  }

  boolean notOutInnverVar(String name) {
    for(int i = 0; i < outerVector.size(); ++ i) {
      if(innerVector.get(i).equals(name)) {
        return false;
      }
    }
    return innerVector.contains(name);
  }

  HashMap<LiavarImpl, Liastar> findParamVars(ArrayList<Liastar> literals) {
    HashMap<LiavarImpl, Liastar> result = new HashMap<>();
    for(int i = 0; i < literals.size(); ++ i) {
      Liastar lit = literals.get(i);
      if(lit instanceof LiaeqImpl) {
        LiaeqImpl equation = (LiaeqImpl) lit;
        if(equation.operand1 instanceof LiavarImpl && equation.operand2 instanceof LiaiteImpl) {
          LiavarImpl var = (LiavarImpl) equation.operand1;
          LiaiteImpl ite = (LiaiteImpl) equation.operand2;
          Liastar iteCond = ite.cond;
          Liastar iteOp1 = ite.operand1;
          Liastar iteOp2 = ite.operand2;
          if(notOutInnverVar(var.varName) && iteOp2.equals(mkConst(innerStar, 0)) && (iteOp1 instanceof LiavarImpl)) {
            Set<String> condVars = iteCond.collectVarSet();
            if(!overLap(condVars, new HashSet<>(innerVector)) && existsOnlyInIteOrEq(literals, var.varName)) {
              result.put(var, ite);
              literals.set(i, null);
            }
          }
        }
      }
    }
    return result;
  }

  Liastar replaceNotZeroCondInItecond(Liastar iteCond, HashMap<LiavarImpl, Liastar> paramNotZeroCond) {
    if (iteCond instanceof LiaandImpl) {
      LiaandImpl tmp = (LiaandImpl) iteCond;
      tmp.operand1 = replaceNotZeroCondInItecond(tmp.operand1, paramNotZeroCond);
      tmp.operand2 = replaceNotZeroCondInItecond(tmp.operand2, paramNotZeroCond);
    } else if (iteCond instanceof LianotImpl)  {
      Liastar body = ((LianotImpl)iteCond).operand;
      if(body instanceof LiaeqImpl) {
        Liastar left = ((LiaeqImpl)body).operand1;
        Liastar right = ((LiaeqImpl)body).operand2;
        if(paramNotZeroCond.containsKey(left) && right.equals(mkConst(innerStar, 0))) {
          LiaiteImpl tmpIte = (LiaiteImpl) paramNotZeroCond.get(left).deepcopy();
          return mkAnd(
              innerStar, tmpIte.cond,
              mkNot(innerStar, mkEq(innerStar, tmpIte.operand1, mkConst(innerStar, 0)))
          );
        }
      }
    }
    return iteCond;
  }

  void replaceNotZeroCondInLit(Liastar literal, HashMap<LiavarImpl, Liastar> paramNotZeroCond) {
    if(literal instanceof LiaeqImpl) {
      LiaeqImpl equation = (LiaeqImpl) literal;
      Liastar eqOp1 = equation.operand1;
      Liastar eqOp2 = equation.operand2;
      if(eqOp2 instanceof LiaiteImpl) {
        LiaiteImpl right = (LiaiteImpl) ((LiaeqImpl)literal).operand2;
        right.cond = replaceNotZeroCondInItecond(right.cond, paramNotZeroCond);
      } else if(eqOp1 instanceof LiavarImpl && paramNotZeroCond.containsKey(eqOp2)){
        equation.operand2 = paramNotZeroCond.get(eqOp2);
      }
    }
  }

  void replaceNotZeroCond(ArrayList<Liastar> literals, HashMap<LiavarImpl, Liastar> paramNotZeroCond) {
    for(Liastar lit : literals) {
      if (lit != null) {
        replaceNotZeroCondInLit(lit, paramNotZeroCond);
      }
    }
  }

  void mergeParameterIte() {
    ArrayList<Liastar> literals = new ArrayList<>();
    decomposeConjunction(constraints, literals);
    HashMap<LiavarImpl, Liastar> paramNotZeroCond = findParamVars(literals);
    replaceNotZeroCond(literals, paramNotZeroCond);
    constraints = mkConjunction(innerStar, literals);
  }

  boolean existsOnlyInItecond(Liastar iteCond, String var) {
    if (iteCond instanceof LiaandImpl) {
      LiaandImpl tmp = (LiaandImpl) iteCond;
      return existsOnlyInItecond(tmp.operand1, var) && existsOnlyInItecond(tmp.operand2, var);
    } else if (iteCond instanceof LianotImpl)  {
      Liastar body = ((LianotImpl)iteCond).operand;
      if(body instanceof LiaeqImpl) {
        Liastar left = ((LiaeqImpl)body).operand1;
        Liastar right = ((LiaeqImpl)body).operand2;
        if(left.equals(mkVar(innerStar, var)) && right.equals(mkConst(innerStar, 0))) {
          return true;
        }
      }
    }
    Set<String> vars = iteCond.collectVarSet();
    return !vars.contains(var);
  }

  boolean existsOnlyInIteOrEqForLiteral(Liastar literal, String var) {
    if(literal instanceof LiaeqImpl) {
      LiaeqImpl equation = (LiaeqImpl) literal;
      Liastar eqOp1 = equation.operand1;
      Liastar eqOp2 = equation.operand2;
      if(eqOp2 instanceof LiaiteImpl) {
        LiaiteImpl ite = (LiaiteImpl) eqOp2;
        Liastar iteOp1 = ite.operand1;
        Set<String> vars = iteOp1.collectVarSet();
        if(vars.contains(var)) {
          return false;
        }
        Liastar iteOp2 = ite.operand2;
        vars = iteOp2.collectVarSet();
        if(vars.contains(var)) {
          return false;
        }
        Liastar iteCond = ite.cond;
        return existsOnlyInItecond(iteCond, var);
      } else if(eqOp1 instanceof LiavarImpl && eqOp2 instanceof LiavarImpl){
        if(((LiavarImpl)eqOp2).varName.equals(var)) {
          return true;
        }
      }
    }
    Set<String> vars = literal.collectVarSet();
    return !vars.contains(var);
  }

  boolean existsOnlyInIteOrEq(ArrayList<Liastar> literals, String var) {
    for(Liastar literal : literals) {
      if(literal != null) {
        if (literal instanceof LiavarImpl && ((LiavarImpl)literal).varName.equals(var)) {
          continue;
        }
        if (!existsOnlyInIteOrEqForLiteral(literal, var)) {
          return false;
        }
      }
    }
    return true;
  }

  boolean isInnerVarEq(String v1, String v2) {
    try (final Context ctx = new Context()) {
      BoolExpr target = null;
      Set<String> varNames = constraints.collectVarSet();
      HashMap<String, IntExpr> varDef = new HashMap<>();
      for (String varName : varNames) {
        IntExpr varExp = ctx.mkIntConst(varName);
        varDef.put(varName, varExp);
      }
      if(!varDef.containsKey(v1) || !varDef.containsKey(v2)) {
        return false;
      }

      BoolExpr formulaF = (BoolExpr) constraints.transToSMT(ctx, varDef);
      BoolExpr v1Eqv2 = ctx.mkEq( varDef.get(v1), varDef.get(v2) );
      target = ctx.mkAnd(formulaF, ctx.mkNot(v1Eqv2));
      Solver s = ctx.mkSolver(ctx.tryFor(ctx.mkTactic("qflia"), SqlSolver.timeout));
      s.add(target);
      Status q = s.check();
      switch(q) {
        case UNSATISFIABLE -> {
          return true;
        }
        case UNKNOWN -> {
          if (LogicSupport.dumpLiaFormulas) {
            System.out.println("fail determine eq for" + v1 + " " + v2);
          }
          return false;
        }
        default -> {
          return false;
        }
      }
    } catch (Exception e) {
      if (LogicSupport.dumpLiaFormulas) {
        System.out.println("fail determine eq for" + v1 + " " + v2);
      }
      return false;
    }
  }

  Liastar nativeExpandstar() {
    Liastar result = null;
    for(int i = 0; i < outerVector.size(); ++ i) {
      String outVar1 = outerVector.get(i);
      String inVar1 = innerVector.get(i);
      for(int j = i + 1; j < outerVector.size(); ++ j) {
        String outVar2 = outerVector.get(j);
        String inVar2 = innerVector.get(j);
        if (isInnerVarEq(inVar1, inVar2)){
          Liastar newExp = mkEq(false, mkVar(false, outVar1), mkVar(false, outVar2));
          result = (result == null) ? newExp : mkAnd(false, result, newExp);
        }
      }
    }
    if(result == null) {
      return mkEq(false, mkConst(false, 0), mkConst(false, 0));
    } else {
      return result;
    }
  }

  public boolean OuterVarsEquals() {
    if (outerVector.size() != 2)
      return false;

    String inVar1 = innerVector.get(0);
    String inVar2 = innerVector.get(1);

    ArrayList<Liastar> literals = new ArrayList<>();
    decomposeConjunction(constraints, literals);
    ArrayList<LiaeqImpl> equations = new ArrayList<>();
    for (Liastar l : literals) {
      if (!(l instanceof LiaeqImpl)) continue;
      LiaeqImpl equation = (LiaeqImpl) l;
      if (equation.operand1 instanceof LiavarImpl && equation.operand2 instanceof LiavarImpl) {
        equations.add(equation);
      }
    }

    HashSet<String> vars = new HashSet<>();
    vars.add(inVar1);
    boolean modified = false;
    do {
      modified = false;
      int size = vars.size();
      for (LiaeqImpl l : equations) {
        String name1 = ((LiavarImpl) l.operand1).varName;
        String name2 = ((LiavarImpl) l.operand2).varName;
        if (vars.contains(name1) || vars.contains(name2)) {
          vars.add(name1);
          vars.add(name2);
        }
      }
      modified = (vars.size() != size);
    } while (modified == true);

    return vars.contains(inVar2);
  }

  @Override
  public Liastar subformulaWithoutStar() {
    return Liastar.mkEq(false, Liastar.mkConst(false, 0), Liastar.mkConst(false, 0));
  }

  @Override
  public int embeddingLayers() {
    return constraints.embeddingLayers() + 1;
  }

  @Override
  public Liastar transformPostOrder(Function<Liastar, Liastar> transformer) {
    Liastar constraints0 = constraints.transformPostOrder(transformer);
    return transformer.apply(mkSum(
            innerStar,
            new ArrayList<>(outerVector),
            new ArrayList<>(innerVector),
            constraints0));
  }

}


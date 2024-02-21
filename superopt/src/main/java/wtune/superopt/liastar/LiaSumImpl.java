package wtune.superopt.liastar;

import com.microsoft.z3.*;
import wtune.superopt.liastar.transformer.LiaTransformer;
import wtune.superopt.logic.LogicSupport;
import wtune.superopt.util.PrettyBuilder;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;

import static wtune.common.utils.IterableSupport.any;


public class LiaSumImpl extends LiaStar {

  ArrayList<String> outerVector;
  ArrayList<String> innerVector;
  LiaStar constraints;

  LiaSumImpl() {
    outerVector = new ArrayList<>();
    innerVector = new ArrayList<>();
    constraints = null;
  }

  @Override
  public LiaStar mergeMult(HashMap<LiaMulImpl, String> multToVar) {
    HashMap<LiaMulImpl, String> curMap = new HashMap<>();
    constraints = constraints.mergeMult(curMap);
    for(LiaMulImpl l : curMap.keySet()) {
      LiaStar result = (LiaVarImpl) mkVar(true, curMap.get(l));
      Set<String> vars = l.collectVarSet();
      for(String v : vars) {
        LiaStar cur = (LiaVarImpl) mkVar(true, v);
        LiaStar newconstr = mkEq(true, cur, mkConst(true, 0));
        newconstr = mkNot(true, newconstr);
        newconstr = mkOr(true, newconstr,
            mkEq(true, result, mkConst(true, 0)));
        constraints = mkAnd(true, constraints, newconstr);
      }

      // (v1 !=0 /\ ... /\ vn !=0) -> (v != 0)
      LiaStar eqzeroConstr = null;
      for(String v : vars) {
        LiaStar cur = (LiaVarImpl) mkVar(true, v);
        LiaStar newconstr = mkEq(true, cur, mkConst(true, 0));
        eqzeroConstr = (eqzeroConstr == null) ? newconstr : mkOr(true, eqzeroConstr, newconstr);
      }
      LiaStar resultNotzero = mkNot(true, mkEq(true, result, mkConst(true, 0)));
      constraints = mkAnd(true, constraints, mkOr(true, eqzeroConstr, resultNotzero) );
    }
    updateInnerVector();

    return this;
  }

  LiaSumImpl(ArrayList<String> v1, ArrayList<String> v2, LiaStar c) {
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
  public LiaStar deepcopy() {
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
  public Set<String> collectAllVars() {
    Set<String> varSet = constraints.collectAllVars();
    varSet.addAll(outerVector);
    return varSet;
  }

  @Override
  public LiaStar multToBin(int n) {
    Set<String> varSet = constraints.collectVarSet();
    int upperBound = 1 << n - 1;
    for(String v : varSet) {
      LiaStar boundCond = mkLe(true, mkVar(true, v), mkConst(true, upperBound));
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
  public LiaStar simplifyMult(HashMap<LiaStar, String> multToVar) {
    constraints.innerStar = true;

    LiaStar tmp = constraints.simplifyMult(multToVar);
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

  /**
   * Expand stars with assistance of an extra constraint.
   * If the extra constraint contradicts with <code>this</code>,
   * it may return a LIA formula representing "false" quickly.
   */
  public LiaStar expandStarWithExtraConstraint(LiaStar extra) {
    // destruct constraints into terms connected by AND
    List<LiaStar> terms = new ArrayList<>();
    if (constraints instanceof LiaAndImpl and) {
      and.flatten(terms);
    } else {
      terms.add(constraints);
    }
    // separate terms with/without star
    LiaStar termLia = null;
    LiaStar termNonLia = null;
    for (LiaStar term : terms) {
      if (term.isLia()) {
        termLia = mkAnd(innerStar, termLia, term);
      } else {
        termNonLia = mkAnd(innerStar, termNonLia, term);
      }
    }
    // expand stars in terms with star
    if (termNonLia != null) {
      termNonLia = termNonLia.expandStar();
    }
    constraints = mkAnd(innerStar, termLia, termNonLia);
    updateInnerVector();
    // transform to LIA
    return new LiaTransformer().transform(extra, outerVector, innerVector, termLia, termNonLia);
  }

  @Override
  public LiaStar expandStar() {
    return expandStarWithExtraConstraint(mkTrue(innerStar));
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
  public Expr transToSMT(Context ctx, Map<String, IntExpr> varsName, Map<String, FuncDecl> funcsName) {
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
    if(!(that instanceof LiaSumImpl))
      return false;
    LiaSumImpl tmp = (LiaSumImpl) that;
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
      LiaStar formula,
      HashSet<String> params,
      HashSet<String> varsWithoutParam,
      ArrayList<LiaStar> conjWithoutParam,
      HashSet<String> varsWithParam,
      ArrayList<LiaStar> conjWithParam
  ) {

    HashSet<String> varsWithoutParam2 = new HashSet<>();
    ArrayList<LiaStar> conjWithoutParam2 = new ArrayList<>();
    HashSet<String> varsWithParam2 = new HashSet<>();
    ArrayList<LiaStar> conjWithParam2 = new ArrayList<>();

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
      LiaStar formula,
      HashSet<String> params,
      HashSet<String> varsWithoutParam,
      ArrayList<LiaStar> conjWithoutParam,
      HashSet<String> varsWithParam,
      ArrayList<LiaStar> conjWithParam
  ) {
    HashSet<String> importantInnerVar = getImportantInnerVars();
    ArrayList<LiaStar> literals = new ArrayList<>();
    decomposeConjunction(formula, literals);
    LiaStar formulaWithoutParams = null;
    LiaStar formulaWithParams = null;
    for(LiaStar lit : literals) {
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
      LiaStar formula,
      HashSet<String> params,
      HashSet<String> varsWithoutParam,
      ArrayList<LiaStar> conjWithoutParam,
      HashSet<String> varsWithParam,
      ArrayList<LiaStar> conjWithParam
  ) {
    ArrayList<LiaStar> conjunctions = decomposeDNF(formula);
    for(LiaStar conj : conjunctions) {
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

  LiaStar buildLinearCombLia(ArrayList<String> result, ArrayList<ArrayList<String>> vectors) {
    LiaStar formula = null;
    for(int i = 0; i < result.size(); ++ i) {
      LiaStar sum = null;
      for(int j = 0; j < vectors.size(); ++ j) {
        LiaStar var = mkVar(innerStar, vectors.get(j).get(i));
        sum = (sum == null) ? var : mkPlus(innerStar, sum, var);
      }
      LiaStar equation = mkEq(innerStar, mkVar(innerStar, result.get(i)), sum);
      formula = (formula == null) ? equation : mkAnd(innerStar, formula, equation);
    }
    assert (formula != null);
    return formula;
  }

  LiaStar zeroVectorLia(ArrayList<String> vector) {
    LiaStar result = null;
    for(String var : vector) {
      LiaStar tmp = mkEq(innerStar, mkVar(innerStar, var), mkConst(innerStar, 0));
      result = (result == null) ? tmp : mkAnd(innerStar, result, tmp);
    }
    return result;
  }

  LiaStar buildOneVectorLia(
      ArrayList<String> xs,
      HashSet<String> ys,
      LiaStar conjWithoutParam,
      LiaStar conjWithParam
  ) {
    LiaStar right = zeroVectorLia(xs);

    ArrayList<String> curOuterVector = new ArrayList<>(xs);
    ArrayList<String> curInnerVector = new ArrayList<>(innerVector);
    LiaStar curConstraint = conjWithoutParam.deepcopy();
    curConstraint.innerStar = innerStar;
    LiaSumImpl star = (LiaSumImpl) mkSum(innerStar, curOuterVector, curInnerVector, curConstraint);
    star.updateInnerVector();

    LiaStar paramLia = replaceParams(conjWithParam, ys, new HashMap<>());

    LiaStar left = mkAnd(innerStar, star, paramLia);

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

  LiaStar buildVectorsLia(
      ArrayList<ArrayList<String>> newVectors,
      HashSet<String> ys,
      ArrayList<LiaStar> conjsWithoutParam,
      ArrayList<LiaStar> conjsWithParam
  ) {
    LiaStar result = null;
    for(int i = 0; i < newVectors.size(); ++ i) {
      ArrayList<String> vector = newVectors.get(i);
      LiaStar conjWithutParam = conjsWithoutParam.get(i);
      LiaStar conjWithParam = conjsWithParam.get(i);
      LiaStar tmp = buildOneVectorLia(vector, ys, conjWithutParam, conjWithParam);
      result = (result == null) ? tmp : mkAnd(innerStar, result, tmp);
    }
    return result;
  }

  LiaStar moveoutParams(
      HashSet<String> ys,
      ArrayList<LiaStar> conjWithoutParam,
      ArrayList<LiaStar> conjWithParam
  ) {
    ArrayList<ArrayList<String>> newVectors = new ArrayList<>();
    for(int i = 0; i < conjWithParam.size(); ++ i) {
      ArrayList<String> newVector = new ArrayList<>();
      newVectors.add(newVector);
      for (int j = 0; j < outerVector.size(); ++j) {
        newVector.add(newVarName());
      }
    }
    LiaStar result = buildLinearCombLia(outerVector, newVectors);

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
        names[j] = LiaStar.newVarName();
      newOuterVars.add(names);
    }
    return newOuterVars;
  }

  LiaStar eqVectorsSum(ArrayList<String> left, ArrayList<String[]> rights) {
    ArrayList<LiaStar> formulas = new ArrayList<>();
    for (String leftVar : left) {
      LiaStar tmp = null;
      LiaVarImpl leftLVar = (LiaVarImpl) LiaStar.mkVar(innerStar, leftVar);
      for (String[] rightVars : rights) {
        LiaVarImpl rightLVar = (LiaVarImpl) LiaStar.mkVar(innerStar, rightVars[0]);
        tmp = (tmp == null) ? rightLVar : LiaStar.mkPlus(innerStar, tmp, rightLVar);
      }
      tmp = LiaStar.mkEq(innerStar, leftLVar, tmp);
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

  private static LiaStar removeParamsFromConjunction(
          boolean innerStar, String[] outerVector, ArrayList<String> innerVector, LiaStar conjunction, HashSet<String> params) {

    ArrayList<LiaStar> literals = new ArrayList<>();
    decomposeConjunction(conjunction, literals);
    HashSet<String> varsOutStar = new HashSet<>(params);
    HashSet<String> varsUnderStar = new HashSet<>(innerVector);
    ArrayList<String> varsMustUnderStar = firstNElements(outerVector.length, innerVector);
    ArrayList<LiaStar> literalsOutStar = new ArrayList<>();
    ArrayList<LiaStar> literalsUnderStar = literals;
    boolean modified = false;
    do {
      modified = false;
      ArrayList<LiaStar> movedLiterals = new ArrayList<>();
      HashSet<String> movedVars = new HashSet<>();
      for (LiaStar l : literalsUnderStar) {
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
    LiaStar newConstraints = constructConjunctions(innerStar, literalsUnderStar);
    ArrayList<String> newInnerVars = new ArrayList(varsMustUnderStar);
    for (String v : newConstraints.collectVarSet()) {
      if (!newInnerVars.contains(v))
        newInnerVars.add(v);
    }
    LiaStar sum = LiaStar.mkSum(innerStar, newOuterVars, newInnerVars, newConstraints);

    LiaStar eqzero = allOuterVarEqZero(newOuterVars);
    LiaStar existsProp = constructConjunctions(innerStar, literalsOutStar);
    LiaStar result = (literalsOutStar.isEmpty()) ? LiaStar.mkAnd(innerStar, sum, existsProp) :
        LiaStar.mkOr(innerStar, eqzero, LiaStar.mkAnd(innerStar, sum, existsProp));

    HashSet<String> exceptVars = new HashSet<>();
    exceptVars.addAll(params);
    exceptVars.addAll(List.of(outerVector));
    result = renameAllVars(result, exceptVars);

    return result;
  }


  private LiaStar removeParamsFromConjunctions(ArrayList<LiaStar> conjunctions, HashSet<String> params) {
    if (conjunctions.isEmpty())
      return null;

    ArrayList<String[]> newOuterVectors = newOuterVarNames(conjunctions.size(), outerVector.size());
    LiaStar eqFormula = eqVectorsSum(outerVector, newOuterVectors);

    ArrayList<LiaStar> results = new ArrayList<>();
    results.add(eqFormula);
    for (int i = 0; i < conjunctions.size(); ++ i) {
      String[] newOuterVector = newOuterVectors.get(i);
      LiaStar tmp = removeParamsFromConjunction(innerStar, newOuterVector, innerVector, conjunctions.get(i), params);
      if (tmp == null) {
        return null;
      } else {
        results.add(tmp);
      }
    }
    return constructConjunctions(innerStar, results);
  }


  @Override
  public LiaStar removeParameter() {
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
      LiaStar tmpConst = constraints.deepcopy();
      tmpConst = paramLiaStar2DNF(tmpConst, true);
      if (LogicSupport.dumpLiaFormulas)
        System.out.println("dnf is" + tmpConst);
      ArrayList<LiaStar> conjunctions = decomposeDNF(tmpConst);
      tmpConst = simplifyDNF(tmpConst);

      HashSet<String> varsWithParam = new HashSet<>();
      HashSet<String> varsWithoutParam = new HashSet<>();
      ArrayList<LiaStar> conjWithParam = new ArrayList<>();
      ArrayList<LiaStar> conjWithoutParam = new ArrayList<>();
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
  public LiaStar removeParameterEager() {
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
      LiaStar tmpConst = constraints.deepcopy();
      tmpConst = paramLiaStar2DNF(tmpConst, true);
      if (LogicSupport.dumpLiaFormulas)
        System.out.println("eager dnf is" + tmpConst);
      ArrayList<LiaStar> conjunctions = decomposeDNF(tmpConst);
      tmpConst = simplifyDNF(tmpConst);

      LiaStar result = removeParamsFromConjunctions(decomposeDNF(tmpConst), params);
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
  public LiaStar simplifyIte() {
    constraints = constraints.simplifyIte();
    return this;
  }

  @Override
  public LiaStar pushUpParameter(HashSet<String> newVars) {
    HashSet<String> newInnerVars = new HashSet<>();
    constraints.pushUpParameter(newInnerVars);
    innerVector.addAll(newInnerVars);
    mergeParameterIte();

    LiaStar newFormula = this;
    for (int i = 0; i < outerVector.size(); i++) {
      LiaStar tmp = pushUpParameterForOneOutVar(i, newVars, constraints);
      if (tmp != null) {
        newFormula = mkAnd(innerStar, newFormula, tmp.deepcopy());
      }
    }

    return newFormula.deepcopy();
  }

  private LiaStar pushUpParameterForOneOutVar(int index, Set<String> newVars, LiaStar formula) {
    switch (formula.getType()) {
      case LAND: {
        final LiaStar eq1 = pushUpParameterForOneOutVar(index, newVars, ((LiaAndImpl)formula).operand1);
        final LiaStar eq2 = pushUpParameterForOneOutVar(index, newVars, ((LiaAndImpl)formula).operand2);
        return mkAnd(innerStar, eq1, eq2);
      }
      case LEQ: {
        // recognize equations like "innerVector[index] = expression"
        final String innerVar = innerVector.get(index);
        final LiaEqImpl equation = (LiaEqImpl) formula;
        final LiaStar left = equation.operand1;
        final LiaStar right = equation.operand2;
        final LiaStar exp;
        boolean varOnLeft = true;
        if (left instanceof LiaVarImpl var && innerVar.equals(var.varName)) {
          exp = right;
        } else if (right instanceof LiaVarImpl var && innerVar.equals(var.varName)) {
          exp = left;
          varOnLeft = false;
        } else {
          return null;
        }
        // the expression should be in certain form
        LiaStar[] result;
        if (exp instanceof LiaVarImpl || exp instanceof LiaMulImpl) {
          // innerVar = v1 * ... * vN
          result = pushUpParameterInIte(index, null, exp, newVars);
        } else if (exp instanceof LiaIteImpl ite) {
          if (!(ite.operand2 instanceof LiaConstImpl)) {
            return null;
          }
          if (((LiaConstImpl) ite.operand2).value != 0) {
            return null;
          }
          // innerVar = ite(..., ..., 0)
          result = pushUpParameterInIte(index, ite.cond, ite.operand1, newVars);
        } else {
          return null;
        }
        // case: no param is pushed up
        if (result == null) {
          return null;
        }
        // otherwise, update exp with result[1]
        if (varOnLeft) {
          equation.operand2 = result[1];
        } else {
          equation.operand1 = result[1];
        }
        // return the part of exp pushed up
        return result[0];
      }
      default: {
        return null;
      }
    }
  }

  // Given
  // (...u...) in {(...u'...) |
  //   u' = ite(condition, trueValue, 0) /\ ...
  // }*
  // where u is outerVector[varIndex] and u' is innerVector[varIndex],
  // try to push up parameters in condition and trueValue.
  // Return [paramExp, updatedIte]
  // where paramExp is the part of expression pushed up outside the star
  // and updatedIte is the remaining part of ite.
  private LiaStar[] pushUpParameterInIte(int varIndex, LiaStar condition, LiaStar trueValue, Set<String> newVars) {
    final LiaStar newCondition0, newTrueValue0; // the updated ite
    final LiaStar newCondition1, newTrueValue1; // pushed up

    // push up parameters in trueValue
    final Set<LiaStar> items = new HashSet<>();
    decomposeMults(trueValue, items);
    LiaStar paramMult = null, innerMult = null;
    for (LiaStar item : items) {
      if (item instanceof LiaVarImpl v && !innerVector.contains(v.varName)) {
        paramMult = (paramMult == null) ? item.deepcopy() : mkMult(true, paramMult, item.deepcopy());
      } else {
        innerMult = (innerMult == null) ? item.deepcopy() : mkMult(true, innerMult, item.deepcopy());
      }
    }
    newTrueValue0 = (innerMult == null) ? mkConst(true, 1) : innerMult;

    // push up parameters in newCondition
    LiaStar[] conds = new LiaStar[2];
    conds[0] = null;
    conds[1] = null;
    if (condition != null) {
      decomposeConditions(condition, conds);
    }
    if (paramMult == null && conds[1] == null) {
      // no param is pushed up; stay unchanged
      return null;
    }
    newCondition0 = conds[0];
    newCondition1 = conds[1];
    final String newOutVarName = newVarName();
    final LiaStar newOutVar = mkVar(innerStar, newOutVarName);
    newTrueValue1 = (paramMult == null) ? newOutVar : mkMult(innerStar, paramMult, newOutVar);

    // construct the result
    final LiaStar oldOutVar = mkVar(innerStar, outerVector.get(varIndex));
    final LiaStar ite1 = newCondition1 == null ? newTrueValue1 :
            mkIte(innerStar, newCondition1, newTrueValue1, mkConst(innerStar, 0));
    final LiaStar paramExp = mkEq(innerStar, oldOutVar, ite1);
    final LiaStar updatedIte = newCondition0 == null ? newTrueValue0 :
            mkIte(innerStar, newCondition0, newTrueValue0, mkConst(innerStar, 0));
    // update states
    newVars.add(newOutVarName);
    outerVector.set(varIndex, newOutVarName);
    return new LiaStar[]{paramExp, updatedIte};
  }

  private void decomposeConditions(LiaStar cond, LiaStar[] condArray) {
    if (cond instanceof LiaAndImpl) {
      decomposeConditions(((LiaAndImpl)cond).operand1, condArray);
      decomposeConditions(((LiaAndImpl)cond).operand2, condArray);
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

  HashMap<LiaVarImpl, LiaStar> findParamVars(ArrayList<LiaStar> literals) {
    HashMap<LiaVarImpl, LiaStar> result = new HashMap<>();
    for(int i = 0; i < literals.size(); ++ i) {
      LiaStar lit = literals.get(i);
      if(lit instanceof LiaEqImpl) {
        LiaEqImpl equation = (LiaEqImpl) lit;
        if(equation.operand1 instanceof LiaVarImpl && equation.operand2 instanceof LiaIteImpl) {
          LiaVarImpl var = (LiaVarImpl) equation.operand1;
          LiaIteImpl ite = (LiaIteImpl) equation.operand2;
          LiaStar iteCond = ite.cond;
          LiaStar iteOp1 = ite.operand1;
          LiaStar iteOp2 = ite.operand2;
          if(notOutInnverVar(var.varName) && iteOp2.equals(mkConst(innerStar, 0)) && (iteOp1 instanceof LiaVarImpl)) {
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

  LiaStar replaceNotZeroCondInItecond(LiaStar iteCond, HashMap<LiaVarImpl, LiaStar> paramNotZeroCond) {
    if (iteCond instanceof LiaAndImpl) {
      LiaAndImpl tmp = (LiaAndImpl) iteCond;
      tmp.operand1 = replaceNotZeroCondInItecond(tmp.operand1, paramNotZeroCond);
      tmp.operand2 = replaceNotZeroCondInItecond(tmp.operand2, paramNotZeroCond);
    } else if (iteCond instanceof LiaNotImpl)  {
      LiaStar body = ((LiaNotImpl)iteCond).operand;
      if(body instanceof LiaEqImpl) {
        LiaStar left = ((LiaEqImpl)body).operand1;
        LiaStar right = ((LiaEqImpl)body).operand2;
        if(paramNotZeroCond.containsKey(left) && right.equals(mkConst(innerStar, 0))) {
          LiaIteImpl tmpIte = (LiaIteImpl) paramNotZeroCond.get(left).deepcopy();
          return mkAnd(
              innerStar, tmpIte.cond,
              mkNot(innerStar, mkEq(innerStar, tmpIte.operand1, mkConst(innerStar, 0)))
          );
        }
      }
    }
    return iteCond;
  }

  void replaceNotZeroCondInLit(LiaStar literal, HashMap<LiaVarImpl, LiaStar> paramNotZeroCond) {
    if(literal instanceof LiaEqImpl) {
      LiaEqImpl equation = (LiaEqImpl) literal;
      LiaStar eqOp1 = equation.operand1;
      LiaStar eqOp2 = equation.operand2;
      if(eqOp2 instanceof LiaIteImpl) {
        LiaIteImpl right = (LiaIteImpl) ((LiaEqImpl)literal).operand2;
        right.cond = replaceNotZeroCondInItecond(right.cond, paramNotZeroCond);
      } else if(eqOp1 instanceof LiaVarImpl && paramNotZeroCond.containsKey(eqOp2)){
        equation.operand2 = paramNotZeroCond.get(eqOp2);
      }
    }
  }

  void replaceNotZeroCond(ArrayList<LiaStar> literals, HashMap<LiaVarImpl, LiaStar> paramNotZeroCond) {
    for(LiaStar lit : literals) {
      if (lit != null) {
        replaceNotZeroCondInLit(lit, paramNotZeroCond);
      }
    }
  }

  void mergeParameterIte() {
    ArrayList<LiaStar> literals = new ArrayList<>();
    decomposeConjunction(constraints, literals);
    HashMap<LiaVarImpl, LiaStar> paramNotZeroCond = findParamVars(literals);
    replaceNotZeroCond(literals, paramNotZeroCond);
    constraints = mkConjunction(innerStar, literals);
  }

  boolean existsOnlyInItecond(LiaStar iteCond, String var) {
    if (iteCond instanceof LiaAndImpl) {
      LiaAndImpl tmp = (LiaAndImpl) iteCond;
      return existsOnlyInItecond(tmp.operand1, var) && existsOnlyInItecond(tmp.operand2, var);
    } else if (iteCond instanceof LiaNotImpl)  {
      LiaStar body = ((LiaNotImpl)iteCond).operand;
      if(body instanceof LiaEqImpl) {
        LiaStar left = ((LiaEqImpl)body).operand1;
        LiaStar right = ((LiaEqImpl)body).operand2;
        if(left.equals(mkVar(innerStar, var)) && right.equals(mkConst(innerStar, 0))) {
          return true;
        }
      }
    }
    Set<String> vars = iteCond.collectVarSet();
    return !vars.contains(var);
  }

  boolean existsOnlyInIteOrEqForLiteral(LiaStar literal, String var) {
    if(literal instanceof LiaEqImpl) {
      LiaEqImpl equation = (LiaEqImpl) literal;
      LiaStar eqOp1 = equation.operand1;
      LiaStar eqOp2 = equation.operand2;
      if(eqOp2 instanceof LiaIteImpl) {
        LiaIteImpl ite = (LiaIteImpl) eqOp2;
        LiaStar iteOp1 = ite.operand1;
        Set<String> vars = iteOp1.collectVarSet();
        if(vars.contains(var)) {
          return false;
        }
        LiaStar iteOp2 = ite.operand2;
        vars = iteOp2.collectVarSet();
        if(vars.contains(var)) {
          return false;
        }
        LiaStar iteCond = ite.cond;
        return existsOnlyInItecond(iteCond, var);
      } else if(eqOp1 instanceof LiaVarImpl && eqOp2 instanceof LiaVarImpl){
        if(((LiaVarImpl)eqOp2).varName.equals(var)) {
          return true;
        }
      }
    }
    Set<String> vars = literal.collectVarSet();
    return !vars.contains(var);
  }

  boolean existsOnlyInIteOrEq(ArrayList<LiaStar> literals, String var) {
    for(LiaStar literal : literals) {
      if(literal != null) {
        if (literal instanceof LiaVarImpl && ((LiaVarImpl)literal).varName.equals(var)) {
          continue;
        }
        if (!existsOnlyInIteOrEqForLiteral(literal, var)) {
          return false;
        }
      }
    }
    return true;
  }

  public boolean OuterVarsEquals() {
    if (outerVector.size() != 2)
      return false;

    String inVar1 = innerVector.get(0);
    String inVar2 = innerVector.get(1);

    ArrayList<LiaStar> literals = new ArrayList<>();
    decomposeConjunction(constraints, literals);
    ArrayList<LiaEqImpl> equations = new ArrayList<>();
    for (LiaStar l : literals) {
      if (!(l instanceof LiaEqImpl)) continue;
      LiaEqImpl equation = (LiaEqImpl) l;
      if (equation.operand1 instanceof LiaVarImpl && equation.operand2 instanceof LiaVarImpl) {
        equations.add(equation);
      }
    }

    HashSet<String> vars = new HashSet<>();
    vars.add(inVar1);
    boolean modified = false;
    do {
      modified = false;
      int size = vars.size();
      for (LiaEqImpl l : equations) {
        String name1 = ((LiaVarImpl) l.operand1).varName;
        String name2 = ((LiaVarImpl) l.operand2).varName;
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
  public LiaStar subformulaWithoutStar() {
    return LiaStar.mkEq(false, LiaStar.mkConst(false, 0), LiaStar.mkConst(false, 0));
  }

  @Override
  public int embeddingLayers() {
    return constraints.embeddingLayers() + 1;
  }

  @Override
  public LiaStar transformPostOrder(Function<LiaStar, LiaStar> transformer) {
    LiaStar constraints0 = constraints.transformPostOrder(transformer);
    return transformer.apply(mkSum(
            innerStar,
            new ArrayList<>(outerVector),
            new ArrayList<>(innerVector),
            constraints0));
  }

  @Override
  public LiaStar transformPostOrder(BiFunction<LiaStar, LiaStar, LiaStar> transformer, LiaStar parent) {
    LiaStar constraints0 = constraints.transformPostOrder(transformer, this);
    return transformer.apply(
            mkSum(innerStar, new ArrayList<>(outerVector), new ArrayList<>(innerVector), constraints0),
            parent);
  }

}


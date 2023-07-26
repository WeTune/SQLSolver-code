package wtune.superopt.liastar;

import com.microsoft.z3.*;

import java.util.*;

public class LiaFuncImpl extends Liastar{

  String funcName;
  List<Liastar> vars;

  LiaFuncImpl(String funcName, Liastar var) {
    this.funcName = funcName;
    this.vars = List.of(var);
  }

  LiaFuncImpl(String funcName, List<Liastar> vars) {
    this.funcName = funcName;
    this.vars = new ArrayList<>(vars);
  }

  @Override
  public boolean isLia() {
    return true;
  }

  @Override
  public Liastar deepcopy() {
    List<Liastar> newVars = new ArrayList<>(vars);
    return Liastar.mkFunc(innerStar, funcName, newVars);
  }

  @Override
  public Liastar multToBin(int n) {
    return this;
  }

  @Override
  public Liastar simplifyMult(HashMap<Liastar, String> multToVar) {
    return null;
  }

  @Override
  public LiaOpType getType() {
    return LiaOpType.LFUNC;
  }

  @Override
  public Liastar mergeMult(HashMap<LiamultImpl, String> multToVar) {
    return this;
  }

  @Override
  public Set<String> collectVarSet() {
    HashSet<String> result = new HashSet<>();
    for (Liastar var : vars)
      result.addAll(var.collectVarSet());
    return result;
  }

  @Override
  public Liastar expandStar() throws Exception {
    return this;
  }

  @Override
  public Expr transToSMT(Context ctx, HashMap<String, IntExpr> varsName) {
    switch (funcName) {
      case "sqrt": {
        final IntExpr varExpr = (IntExpr) vars.get(0).transToSMT(ctx, varsName);
        RealExpr realExpr = ctx.mkInt2Real(varExpr);
        FPExpr fpExpr = ctx.mkFPToFP(ctx.mkFPRoundNearestTiesToEven(), realExpr, ctx.mkFPSortDouble());
        Expr result = ctx.mkFPSqrt(ctx.mkFPRoundNearestTiesToEven(), fpExpr);
        result = ctx.mkFPToReal((FPExpr) result);
        return ctx.mkReal2Int((RealExpr) result);
      }
      case "minus": {
        final IntExpr varExpr0 = (IntExpr) vars.get(0).transToSMT(ctx, varsName);
        final IntExpr varExpr1 = (IntExpr) vars.get(1).transToSMT(ctx, varsName);
        return ctx.mkSub(varExpr0, varExpr1);
      }
      default: {
        final IntExpr varExpr = (IntExpr) vars.get(0).transToSMT(ctx, varsName);
        final Sort I = ctx.getIntSort();
        final FuncDecl func = ctx.mkFuncDecl(funcName, I, I);
        return ctx.mkApp(func, varExpr);
      }
    }
  }

  @Override
  public EstimateResult estimate() {
    // Unsupport
    return null;
  }

  @Override
  public Expr expandStarWithK(Context ctx, Solver sol, String suffix) {
    // Unsupport
    return null;
  }

  @Override
  public Set<String> getVars() {
    HashSet<String> result = new HashSet<>();
    for (Liastar var : vars)
      result.addAll(var.getVars());
    return result;
  }

  @Override
  public String toString() {
    String result = funcName + "(";
    for (Liastar var : vars) {
      result = result + var.toString() + ",";
    }
    return result + ")";
  }

  @Override
  public boolean equals(Object that) {
    if(that == this)
      return true;
    if(that == null)
      return false;
    if(!(that instanceof LiaFuncImpl))
      return false;
    LiaFuncImpl tmp = (LiaFuncImpl) that;
    return funcName.equals(tmp.funcName) && vars.equals(tmp.vars);
  }

  @Override
  public int hashCode() {
    return vars.hashCode();
  }

}

package wtune.superopt.liastar;

import com.microsoft.z3.*;
import wtune.superopt.util.PrettyBuilder;

import java.util.*;
import java.util.function.Function;

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

  private Expr transFuncToSMT(Context ctx, HashMap<String, IntExpr> varsName) {
    // sorts
    final Sort I = ctx.getIntSort();
    Sort[] argSorts = new Sort[vars.size()];
    Arrays.fill(argSorts, I);
    // args
    Expr[] args = vars.stream().map(x -> x.transToSMT(ctx, varsName))
            .toList().toArray(new Expr[0]);
    // func app
    final FuncDecl func = ctx.mkFuncDecl(funcName, argSorts, I);
    return ctx.mkApp(func, args);
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
        return transFuncToSMT(ctx, varsName);
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
  protected void prettyPrint(PrettyBuilder builder) {
    int indent = funcName.length() + 1;
    builder.print(funcName).print("(").indent(indent);
    for (int i = 0, bound = vars.size(); i < bound; i++) {
      Liastar var = vars.get(i);
      boolean multiLine = var.isPrettyPrintMultiLine();
      if (i > 0 && multiLine) builder.println();
      var.prettyPrint(builder);
      if (i < bound - 1) builder.print(", ");
      if (multiLine) builder.println();
    }
    builder.indent(-indent).print(")");
  }

  @Override
  protected boolean isPrettyPrintMultiLine() {
    for (Liastar var : vars) {
      if (var.isPrettyPrintMultiLine()) return true;
    }
    return false;
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

  @Override
  public int embeddingLayers() {
    return 0;
  }

  @Override
  public Liastar transformPostOrder(Function<Liastar, Liastar> transformer) {
    List<Liastar> newVars = new ArrayList<>(vars.stream().map(v -> v.transformPostOrder(transformer)).toList());
    return transformer.apply(mkFunc(innerStar, funcName, newVars));
  }

}

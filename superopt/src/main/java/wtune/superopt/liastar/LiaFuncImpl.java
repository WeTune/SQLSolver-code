package wtune.superopt.liastar;

import com.microsoft.z3.*;
import wtune.superopt.util.PrettyBuilder;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;

public class LiaFuncImpl extends LiaStar {

  String funcName;
  List<LiaStar> vars;

  LiaFuncImpl(String funcName, LiaStar var) {
    this.funcName = funcName;
    this.vars = List.of(var);
  }

  LiaFuncImpl(String funcName, List<LiaStar> vars) {
    this.funcName = funcName;
    this.vars = new ArrayList<>(vars);
  }

  @Override
  public boolean isLia() {
    return true;
  }

  @Override
  public LiaStar deepcopy() {
    List<LiaStar> newVars = new ArrayList<>(vars);
    return LiaStar.mkFunc(innerStar, funcName, newVars);
  }

  @Override
  public LiaStar multToBin(int n) {
    return this;
  }

  @Override
  public LiaStar simplifyMult(HashMap<LiaStar, String> multToVar) {
    return null;
  }

  @Override
  public LiaOpType getType() {
    return LiaOpType.LFUNC;
  }

  @Override
  public LiaStar mergeMult(HashMap<LiaMulImpl, String> multToVar) {
    return this;
  }

  @Override
  public Set<String> collectVarSet() {
    HashSet<String> result = new HashSet<>();
    for (LiaStar var : vars)
      result.addAll(var.collectVarSet());
    return result;
  }

  @Override
  public Set<String> collectAllVars() {
    HashSet<String> result = new HashSet<>();
    for (LiaStar var : vars)
      result.addAll(var.collectAllVars());
    return result;
  }

  @Override
  public LiaStar expandStar() {
    return this;
  }

  private Expr transFuncToSMT(Context ctx, Map<String, IntExpr> varsName, Map<String, FuncDecl> funcsName) {
    // args
    Expr[] args = vars.stream().map(x -> x.transToSMT(ctx, varsName, funcsName))
            .toList().toArray(new Expr[0]);
    // func app
    FuncDecl func = funcsName.get(funcName);
    if (func == null) {
      // create function definition upon first use
      final Sort I = ctx.getIntSort();
      Sort[] argSorts = new Sort[vars.size()];
      Arrays.fill(argSorts, I);
      func = ctx.mkFuncDecl(funcName, argSorts, I);
      funcsName.put(funcName, func);
    }
    return ctx.mkApp(func, args);
  }

  @Override
  public Expr transToSMT(Context ctx, Map<String, IntExpr> varsName, Map<String, FuncDecl> funcsName) {
    switch (funcName) {
      case "sqrt": {
        final IntExpr varExpr = (IntExpr) vars.get(0).transToSMT(ctx, varsName, funcsName);
        RealExpr realExpr = ctx.mkInt2Real(varExpr);
        FPExpr fpExpr = ctx.mkFPToFP(ctx.mkFPRoundNearestTiesToEven(), realExpr, ctx.mkFPSortDouble());
        Expr result = ctx.mkFPSqrt(ctx.mkFPRoundNearestTiesToEven(), fpExpr);
        result = ctx.mkFPToReal((FPExpr) result);
        return ctx.mkReal2Int((RealExpr) result);
      }
      case "minus": {
        final IntExpr varExpr0 = (IntExpr) vars.get(0).transToSMT(ctx, varsName, funcsName);
        final IntExpr varExpr1 = (IntExpr) vars.get(1).transToSMT(ctx, varsName, funcsName);
        return ctx.mkSub(varExpr0, varExpr1);
      }
      default: {
        return transFuncToSMT(ctx, varsName, funcsName);
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
    for (LiaStar var : vars)
      result.addAll(var.getVars());
    return result;
  }

  @Override
  protected void prettyPrint(PrettyBuilder builder) {
    int indent = funcName.length() + 1;
    builder.print(funcName).print("(").indent(indent);
    for (int i = 0, bound = vars.size(); i < bound; i++) {
      LiaStar var = vars.get(i);
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
    for (LiaStar var : vars) {
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
  public LiaStar transformPostOrder(Function<LiaStar, LiaStar> transformer) {
    List<LiaStar> newVars = new ArrayList<>(vars.stream().map(v -> v.transformPostOrder(transformer)).toList());
    return transformer.apply(mkFunc(innerStar, funcName, newVars));
  }

  @Override
  public LiaStar transformPostOrder(BiFunction<LiaStar, LiaStar, LiaStar> transformer, LiaStar parent) {
    List<LiaStar> newVars = new ArrayList<>(vars.stream().map(v -> v.transformPostOrder(transformer, this)).toList());
    return transformer.apply(mkFunc(innerStar, funcName, newVars), parent);
  }

}

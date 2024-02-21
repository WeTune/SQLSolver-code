package wtune.superopt.liastar;

import com.microsoft.z3.*;
import wtune.superopt.util.PrettyBuilder;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;

public class LiaVarImpl extends LiaStar {

  String varName;

  @Override
  public int embeddingLayers() {
    return 0;
  }

  @Override
  public Set<String> collectVarSet() {
    Set<String> varSet = new HashSet<>();
    varSet.add(varName);
    return varSet;
  }

  @Override
  public Set<String> collectAllVars() {
    Set<String> varSet = new HashSet<>();
    varSet.add(varName);
    return varSet;
  }

  @Override
  public LiaStar mergeMult(HashMap<LiaMulImpl, String> multToVar) {
    return this;
  }


  public LiaVarImpl() {
    varName = "";
  }

  public LiaVarImpl(String s) {
    varName = s;
  }

  String getValue() {
    return varName;
  }

  @Override
  public boolean isLia() {
    return true;
  }

  @Override
  protected void prettyPrint(PrettyBuilder builder) {
    builder.print(varName);
  }

  @Override
  protected boolean isPrettyPrintMultiLine() {
    return false;
  }

  @Override
  public LiaOpType getType() {
    return LiaOpType.LVAR;
  }

  @Override
  public Set<String> getVars() {
    Set<String> result = new HashSet<>();
    result.add(varName);
    return result;
  }

  public String getName() {
    return varName;
  }

  @Override
  public LiaStar deepcopy() {
    return mkVar(innerStar, varName);
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
  public boolean equals(Object that) {
    if(that == this)
      return true;
    if(that == null)
      return false;
    if(!(that instanceof LiaVarImpl))
      return false;
    LiaVarImpl tmp = (LiaVarImpl) that;
    return varName.equals(tmp.varName);
  }

  @Override
  public int hashCode() {
    return varName.hashCode();
  }

  @Override
  public LiaStar expandStar() {
    return this;
  }

  @Override
  public Expr transToSMT(Context ctx, Map<String, IntExpr> varsName, Map<String, FuncDecl> funcsName) {
    return varsName.get(varName);
  }

  @Override
  public EstimateResult estimate() {
    return new EstimateResult(
            new HashSet(List.of(varName)),
            0,
            0,
            1
    );
  }

  @Override
  public Expr expandStarWithK(Context ctx, Solver sol, String suffix) {
    return ctx.mkIntConst(varName + suffix);
  }

  @Override
  public LiaStar transformPostOrder(Function<LiaStar, LiaStar> transformer) {
    return transformer.apply(mkVar(innerStar, varName));
  }

  @Override
  public LiaStar transformPostOrder(BiFunction<LiaStar, LiaStar, LiaStar> transformer, LiaStar parent) {
    return transformer.apply(mkVar(innerStar, varName), parent);
  }
}

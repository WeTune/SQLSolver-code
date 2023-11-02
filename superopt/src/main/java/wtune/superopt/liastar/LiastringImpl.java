package wtune.superopt.liastar;

import com.microsoft.z3.*;
import wtune.superopt.util.PrettyBuilder;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;

public class LiastringImpl extends Liastar {

  String value;

  LiastringImpl() {
    value = "";
  }

  LiastringImpl(String v) {
    value = v;
  }

  @Override
  public boolean isLia() {
    return true;
  }

  @Override
  public LiaOpType getType() {
    return LiaOpType.LSTRING;
  }

  public String getValue() {
    return value;
  }

  @Override
  public Set<String> collectVarSet() {
    return new HashSet<>();
  }

  @Override
  public Liastar mergeMult(HashMap<LiamultImpl, String> multToVar) {
    return this;
  }

  @Override
  public Set<String> getVars() {
    return new HashSet<>();
  }

  @Override
  public Liastar deepcopy() {
    return mkString(innerStar, value);
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
  public boolean equals(Object that) {
    if(that == this)
      return true;
    if(that == null)
      return false;
    if(!(that instanceof LiastringImpl tmp))
      return false;
    return Objects.equals(value, tmp.value);
  }

  @Override
  public int hashCode() {
    return Math.toIntExact(value.hashCode());
  }

  @Override
  protected void prettyPrint(PrettyBuilder builder) {
    builder.print(value);
  }

  @Override
  protected boolean isPrettyPrintMultiLine() {
    return false;
  }

  @Override
  public Liastar expandStar() throws Exception {
    return this;
  }

  @Override
  public Expr transToSMT(Context ctx, HashMap<String, IntExpr> varsName) {
    return ctx.mkString(value);
  }

  @Override
  public EstimateResult estimate() {
    return null;
  }

  @Override
  public Expr expandStarWithK(Context ctx, Solver sol, String suffix) {
    return null;
  }

  @Override
  public int embeddingLayers() {
    return 0;
  }

  @Override
  public Liastar transformPostOrder(Function<Liastar, Liastar> transformer) {
    return transformer.apply(mkString(innerStar, value));
  }
}

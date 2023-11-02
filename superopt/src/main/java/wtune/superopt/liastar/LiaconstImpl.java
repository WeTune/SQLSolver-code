package wtune.superopt.liastar;

import com.microsoft.z3.*;
import wtune.superopt.util.PrettyBuilder;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

public class LiaconstImpl extends Liastar {

  long value;

  LiaconstImpl() {
    value = 0;
  }

  LiaconstImpl(long v) {
    value = v;
  }

  @Override
  public boolean isLia() {
    return true;
  }

  @Override
  public LiaOpType getType() {
    return LiaOpType.LCONST;
  }

  public long getValue() {
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
    return mkConst(innerStar, value);
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
    if(!(that instanceof LiaconstImpl))
      return false;
    LiaconstImpl tmp = (LiaconstImpl) that;
    return value == tmp.value;
  }

  @Override
  public int hashCode() {
    return Math.toIntExact(value % 10000);
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
    return ctx.mkInt(value);
  }

  @Override
  public EstimateResult estimate() {
    return new EstimateResult(
            new HashSet(),
            0,
            0,
            value
    );
  }

  @Override
  public Expr expandStarWithK(Context ctx, Solver sol, String suffix) {
    return ctx.mkInt(value);
  }


  @Override
  public int embeddingLayers() {
    return 0;
  }

  @Override
  public Liastar transformPostOrder(Function<Liastar, Liastar> transformer) {
    return transformer.apply(mkConst(innerStar, value));
  }

}

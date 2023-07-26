package wtune.superopt.liastar;

import com.microsoft.z3.*;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

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
  public String toString() {
    return String.valueOf(value);
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


}

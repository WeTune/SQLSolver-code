package wtune.superopt.liastar;

import com.microsoft.z3.*;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

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
  public String toString() {
    return String.valueOf(value);
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


}

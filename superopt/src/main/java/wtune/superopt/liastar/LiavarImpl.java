package wtune.superopt.liastar;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.Solver;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class LiavarImpl extends Liastar {

  public String varName;

  @Override
  public Set<String> collectVarSet() {
    Set<String> varSet = new HashSet<>();
    varSet.add(varName);
    return varSet;
  }

  @Override
  public Liastar mergeMult(HashMap<LiamultImpl, String> multToVar) {
    return this;
  }


  public LiavarImpl() {
    varName = "";
  }

  public LiavarImpl(String s) {
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
  public String toString() {
    return varName;
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

  @Override
  public Liastar deepcopy() {
    return mkVar(innerStar, varName);
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
    if(!(that instanceof LiavarImpl))
      return false;
    LiavarImpl tmp = (LiavarImpl) that;
    return varName.equals(tmp.varName);
  }

  @Override
  public int hashCode() {
    return varName.hashCode();
  }

  @Override
  public Liastar expandStar() throws Exception {
    return this;
  }

  @Override
  public Expr transToSMT(Context ctx, HashMap<String, IntExpr> varsName) {
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
}

package wtune.superopt.liastar;

import com.microsoft.z3.*;
import wtune.superopt.util.PrettyBuilder;

import java.util.*;
import java.util.function.Function;


public class LiaplusImpl extends Liastar {

  Liastar operand1;
  Liastar operand2;

  LiaplusImpl(Liastar op1, Liastar op2) {
    operand1 = op1;
    operand2 = op2;
  }

  @Override
  public Liastar mergeMult(HashMap<LiamultImpl, String> multToVar) {
    operand1 = operand1.mergeMult(multToVar);
    operand2 = operand2.mergeMult(multToVar);
    return this;
  }

  @Override
  public boolean isLia() {
    return true;
  }

  @Override
  public LiaOpType getType() {
    return LiaOpType.LPLUS;
  }

  @Override
  public Set<String> getVars() {
    Set<String> result = operand1.getVars();
    result.addAll(operand2.getVars());
    return result;
  }

  @Override
  public Liastar deepcopy() {
    return mkPlus(innerStar, operand1.deepcopy(), operand2.deepcopy());
  }

  @Override
  protected void prettyPrint(PrettyBuilder builder) {
    prettyPrintBinaryOp(builder, operand1, operand2,
            false, false, " + ");
  }

  @Override
  protected boolean isPrettyPrintMultiLine() {
    return operand1.isPrettyPrintMultiLine()
            || operand2.isPrettyPrintMultiLine();
  }

  @Override
  public Set<String> collectVarSet() {
    Set<String> varSet = operand1.collectVarSet();
    varSet.addAll(operand2.collectVarSet());
    return varSet;
  }

  @Override
  public Liastar multToBin(int n) {
    operand1 = operand1.multToBin(n);
    operand2 = operand2.multToBin(n);
    return this;
  }

  @Override
  public Liastar simplifyMult(HashMap<Liastar, String> multToVar) {
    operand1.innerStar = innerStar;
    operand2.innerStar = innerStar;
    Liastar[] tmp = new Liastar[2];
    tmp[0] = operand1.simplifyMult(multToVar);
    tmp[1] = operand2.simplifyMult(multToVar);
    return liaAndConcat(tmp);
  }

  @Override
  public Liastar expandStar() throws Exception {
    return this;
  }

  @Override
  public Expr transToSMT(Context ctx, HashMap<String, IntExpr> varsName) {
    Expr one = operand1.transToSMT(ctx, varsName);
    Expr two = operand2.transToSMT(ctx, varsName);
    return ctx.mkAdd((ArithExpr) one, (ArithExpr) two);
  }

  @Override
  public EstimateResult estimate() {
    EstimateResult r1 = operand1.estimate();
    EstimateResult r2 = operand2.estimate();
    r1.vars.addAll(r2.vars);
    return new EstimateResult(
            r1.vars,
            r1.n_extra + r2.n_extra,
            r1.m + r2.m,
            Math.max(r1.a, r2.a)
    );
  }

  @Override
  public Expr expandStarWithK(Context ctx, Solver sol, String suffix) {
    return ctx.mkAdd(
            (ArithExpr)operand1.expandStarWithK(ctx, sol, suffix),
            (ArithExpr)operand2.expandStarWithK(ctx, sol, suffix)
    );
  }


  @Override
  public boolean equals(Object obj) {
    if(obj == this)
      return true;
    if(obj == null)
      return false;
    if(!(obj instanceof LiaplusImpl))
      return false;
    LiaplusImpl that = (LiaplusImpl) obj;
    HashSet<Liastar> thisItems = new HashSet<>();
    HashSet<Liastar> thatItems = new HashSet<>();
    decomposePluses(this, thisItems);
    decomposePluses(that, thatItems);
    for(Liastar formula : thisItems) {
      if(!thatItems.contains(formula)) {
        return false;
      }
    }
    for(Liastar formula : thatItems) {
      if(!thisItems.contains(formula)) {
        return false;
      }
    }
    return true;
  }

  @Override
  public int hashCode() {
    HashSet<Liastar> thisItems = new HashSet<>();
    decomposePluses(this, thisItems);
    int result = 0;
    for(Liastar formula : thisItems) {
      result = result + formula.hashCode();
    }
    return result;
  }

  @Override
  public Liastar simplifyIte() {
    operand1 = operand1.simplifyIte();
    operand2 = operand2.simplifyIte();
    Liastar tmpZero = mkConst(innerStar, 0);
    if (operand1.equals(tmpZero)) {
      return operand2;
    }
    if (operand2.equals(tmpZero)) {
      return operand1;
    }
    return this;
  }

  @Override
  public int embeddingLayers() {
    return 0;
  }

  @Override
  public Liastar transformPostOrder(Function<Liastar, Liastar> transformer) {
    Liastar operand10 = operand1.transformPostOrder(transformer);
    Liastar operand20 = operand2.transformPostOrder(transformer);
    return transformer.apply(mkPlus(innerStar, operand10, operand20));
  }

}

package wtune.superopt.liastar;

import com.microsoft.z3.*;
import wtune.superopt.util.PrettyBuilder;

import java.util.HashMap;
import java.util.Set;
import java.util.function.Function;

public class LiaeqImpl extends Liastar {

  Liastar operand1;
  Liastar operand2;


  LiaeqImpl(Liastar op1, Liastar op2) {
    operand1 = op1;
    operand2 = op2;
  }

  @Override
  public Set<String> collectVarSet() {
    Set<String> varSet = operand1.collectVarSet();
    varSet.addAll(operand2.collectVarSet());
    return varSet;
  }

  @Override
  protected void prettyPrint(PrettyBuilder builder) {
    prettyPrintBinaryOp(builder, operand1, operand2,
            false, false, " = ");
  }

  @Override
  protected boolean isPrettyPrintMultiLine() {
    return operand1.isPrettyPrintMultiLine()
            || operand2.isPrettyPrintMultiLine();
  }

  @Override
  public LiaOpType getType() {
    return LiaOpType.LEQ;
  }

  @Override
  public boolean isLia() {
    return true;
  }

  @Override
  public Set<String> getVars() {
    Set<String> result = operand1.getVars();
    result.addAll(operand2.getVars());
    return result;
  }

  @Override
  public Liastar deepcopy() {
    return mkEq(innerStar, operand1.deepcopy(), operand2.deepcopy());
  }

  @Override
  public Liastar mergeMult(HashMap<LiamultImpl, String> multToVar) {
    operand1 = operand1.mergeMult(multToVar);
    operand2 = operand2.mergeMult(multToVar);
    return this;
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
  public boolean equals(Object that) {
    if(that == this)
      return true;
    if(that == null)
      return false;
    if(!(that instanceof LiaeqImpl))
      return false;
    LiaeqImpl tmp = (LiaeqImpl) that;
    return operand1.equals(tmp.operand1) && operand2.equals(tmp.operand2);
  }

  @Override
  public int hashCode() {
    return operand1.hashCode() + operand2.hashCode();
  }

  @Override
  public Liastar expandStar() throws Exception {
    return this;
  }

  @Override
  public Expr transToSMT(Context ctx, HashMap<String, IntExpr> varsName) {
    Expr c1 = operand1.transToSMT(ctx, varsName);
    Expr c2 = operand2.transToSMT(ctx, varsName);
    return ctx.mkEq(c1, c2);
  }

  @Override
  public EstimateResult estimate() {
    EstimateResult r1 = operand1.estimate();
    EstimateResult r2 = operand2.estimate();
    r1.vars.addAll(r2.vars);
    return new EstimateResult(
            r1.vars,
            r1.n_extra + r2.n_extra,
            r1.m + r2.m + 1,
            Math.max(r1.a, r2.a)
    );
  }

  @Override
  public Expr expandStarWithK(Context ctx, Solver sol, String suffix) {
    return ctx.mkEq(
            operand1.expandStarWithK(ctx, sol, suffix),
            operand2.expandStarWithK(ctx, sol, suffix)
    );
  }


  @Override
  public Liastar simplifyIte() {
    operand1 = operand1.simplifyIte();
    operand2 = operand2.simplifyIte();

    if(operand1 instanceof LiaiteImpl) {
      LiaiteImpl iteLia = (LiaiteImpl) operand1;
      Liastar iteOp1 = iteLia.operand1;
      Liastar iteOp2 = iteLia.operand2;
      if((iteOp1 instanceof LiaconstImpl) && (iteOp2 instanceof LiaconstImpl)) {
        if (iteOp1.equals(operand2)) {
          return iteLia.cond.deepcopy();
        } else if (iteOp2.equals(operand2)) {
          return mkNot(innerStar, iteLia.cond.deepcopy());
        }
      }
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
    return transformer.apply(mkEq(innerStar, operand10, operand20));
  }

}

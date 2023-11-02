package wtune.superopt.liastar;

import com.microsoft.z3.*;
import wtune.superopt.util.PrettyBuilder;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

public class LiadivImpl extends Liastar {
  Liastar operand1;
  Liastar operand2;

  LiadivImpl(Liastar op1, Liastar op2) {
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
    return LiaOpType.LDIV;
  }

  @Override
  public Set<String> getVars() {
    Set<String> result = operand1.getVars();
    result.addAll(operand2.getVars());
    return result;
  }

  @Override
  public Liastar deepcopy() {
    return mkDiv(innerStar, operand1.deepcopy(), operand2.deepcopy());
  }

  @Override
  protected void prettyPrint(PrettyBuilder builder) {
    boolean needsParen1 = (operand1 instanceof LiaplusImpl);
    boolean needsParen2 = (operand1 instanceof LiaplusImpl);
    prettyPrintBinaryOp(builder, operand1, operand2,
            needsParen1, needsParen2, " / ");
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
    assert innerStar == false;
    return this;
  }

  @Override
  public Liastar expandStar() throws Exception {
    return this;
  }

  @Override
  public Expr transToSMT(Context ctx, HashMap<String, IntExpr> varsName) {
    Expr one = operand1.transToSMT(ctx, varsName);
    Expr two = operand2.transToSMT(ctx, varsName);
    return ctx.mkDiv((ArithExpr) one, (ArithExpr) two);
  }

  @Override
  public Liastar.EstimateResult estimate() {
    assert false;
    System.err.println("Estimate not support division !!!");
    return null;
  }

  @Override
  public Expr expandStarWithK(Context ctx, Solver sol, String suffix) {
    assert false;
    System.err.println("Estimate not support division !!!");
    return null;
  }


  @Override
  public boolean equals(Object obj) {
    if(obj == this)
      return true;
    if(obj == null)
      return false;
    if(!(obj instanceof LiadivImpl))
      return false;
    LiadivImpl that = (LiadivImpl) obj;
    return operand1.equals(that.operand1) && operand2.equals(that.operand2);
  }

  @Override
  public int hashCode() {
    int result = 0;
    result = result + operand1.hashCode();
    result = result + operand2.hashCode();
    return result;
  }

  @Override
  public Liastar simplifyIte() {
    operand1 = operand1.simplifyIte();
    operand2 = operand2.simplifyIte();
    Liastar tmpZero = mkConst(innerStar, 0);
    if (operand1.equals(tmpZero)) {
      return tmpZero;
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
    return transformer.apply(mkDiv(innerStar, operand10, operand20));
  }

}

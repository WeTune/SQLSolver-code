package wtune.superopt.liastar;

import com.microsoft.z3.*;
import wtune.superopt.util.PrettyBuilder;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

public class LianotImpl extends Liastar {

  Liastar operand;

  LianotImpl(Liastar op) {
    operand = op;
  }

  @Override
  public LiaOpType getType() {
    return LiaOpType.LNOT;
  }

  @Override
  public boolean isLia() {
    return operand.isLia();
  }

  @Override
  public Set<String> getVars() {
    return operand.getVars();
  }

  @Override
  public Liastar deepcopy() {
    return mkNot(innerStar, operand.deepcopy());
  }

  @Override
  protected void prettyPrint(PrettyBuilder builder) {
    builder.print("~(").indent(2);
    operand.prettyPrint(builder);
    builder.indent(-2).print(")");
  }

  @Override
  protected boolean isPrettyPrintMultiLine() {
    return operand.isPrettyPrintMultiLine();
  }

  @Override
  public Set<String> collectVarSet() {
    return operand.collectVarSet();
  }

  @Override
  public Liastar multToBin(int n) {
    operand = operand.multToBin(n);
    return this;
  }

  @Override
  public Liastar expandStar() throws Exception {
    return this;
  }

  @Override
  public Liastar simplifyMult(HashMap<Liastar, String> multToVar) {
    operand.innerStar = innerStar;
    return operand.simplifyMult(multToVar);
  }

  @Override
  public Liastar mergeMult(HashMap<LiamultImpl, String> multToVar) {
    operand = operand.mergeMult(multToVar);
    return this;
  }

  @Override
  public Expr transToSMT(Context ctx, HashMap<String, IntExpr> varsName) {
    Expr one = operand.transToSMT(ctx, varsName);
    return ctx.mkNot((BoolExpr) one);
  }

  @Override
  public EstimateResult estimate() {
    if (operand instanceof LiaandImpl) {
      Liastar op1 = ((LiaandImpl) operand).operand1;
      Liastar op2 = ((LiaandImpl) operand).operand2;
      return Liastar.mkOr(innerStar,
              Liastar.mkNot(innerStar, op1),
              Liastar.mkNot(innerStar, op2)
      ).estimate();
    } else if (operand instanceof LiaeqImpl) {
      Liastar op1 = ((LiaeqImpl) operand).operand1;
      Liastar op2 = ((LiaeqImpl) operand).operand2;
      return Liastar.mkOr(innerStar,
              Liastar.mkLt(innerStar, op1, op2),
              Liastar.mkLt(innerStar, op2, op1)
      ).estimate();
    } else if (operand instanceof LialeImpl) {
      Liastar op1 = ((LialeImpl) operand).operand1;
      Liastar op2 = ((LialeImpl) operand).operand2;
      return Liastar.mkLt(innerStar, op2, op1).estimate();
    } else if (operand instanceof LialtImpl) {
      Liastar op1 = ((LialtImpl) operand).operand1;
      Liastar op2 = ((LialtImpl) operand).operand2;
      return Liastar.mkLe(innerStar, op2, op1).estimate();
    } else if (operand instanceof LianotImpl) {
      return ((LianotImpl) operand).operand.estimate();
    } else if (operand instanceof LiaorImpl) {
      Liastar op1 = ((LiaorImpl) operand).operand1;
      Liastar op2 = ((LiaorImpl) operand).operand2;
      return Liastar.mkAnd(innerStar,
              Liastar.mkNot(innerStar, op1),
              Liastar.mkNot(innerStar, op2)
      ).estimate();
    } else {
      throw new RuntimeException("Using not onto non-logical expression or sum");
    }
  }

  @Override
  public Expr expandStarWithK(Context ctx, Solver sol, String suffix) {
    return ctx.mkNot(
            (BoolExpr)operand.expandStarWithK(ctx, sol, suffix)
    );
  }

  @Override
  public boolean equals(Object that) {
    if(that == this)
      return true;
    if(that == null)
      return false;
    if(!(that instanceof LianotImpl))
      return false;
    LianotImpl tmp = (LianotImpl) that;
    return operand.equals(tmp.operand);
  }

  @Override
  public int hashCode() {
    return operand.hashCode();
  }

  @Override
  public void prepareInnervector(HashSet<String> vars) {
    operand.prepareInnervector(vars);
  }

  @Override
  public Liastar removeParameter() {
    operand = operand.removeParameter();
    return this;
  }

  @Override
  public Liastar removeParameterEager() {
    operand = operand.removeParameterEager();
    return this;
  }

  @Override
  public Liastar pushUpParameter(HashSet<String> newVars) {
    operand = operand.pushUpParameter(newVars);
    return this;
  }

  @Override
  public HashSet<String> collectParams() {
    return operand.collectParams();
  }

  @Override
  public Liastar simplifyIte() {
    operand = operand.simplifyIte();
    if(operand instanceof LianotImpl) {
      LianotImpl tmp = (LianotImpl) operand;
      return tmp.operand.deepcopy();
    }
    return this;
  }

  @Override
  public int embeddingLayers() {
    return operand.embeddingLayers();
  }

  @Override
  public Liastar transformPostOrder(Function<Liastar, Liastar> transformer) {
    Liastar operand0 = operand.transformPostOrder(transformer);
    return transformer.apply(mkNot(innerStar, operand0));
  }

}

package wtune.superopt.liastar;

import com.microsoft.z3.*;
import wtune.superopt.util.PrettyBuilder;

import java.util.*;
import java.util.function.Function;

public class LiaiteImpl extends Liastar {

  Liastar cond;
  Liastar operand1;
  Liastar operand2;


  LiaiteImpl(Liastar c, Liastar op1, Liastar op2) {
    cond = c;
    operand1 = op1;
    operand2 = op2;
  }

  @Override
  public Set<String> collectVarSet() {
    Set<String> varSet = operand1.collectVarSet();
    varSet.addAll(operand2.collectVarSet());
    varSet.addAll(cond.collectVarSet());
    return varSet;
  }

  @Override
  protected void prettyPrint(PrettyBuilder builder) {
    builder.print("ite(").indent(4);

    boolean multiLine = cond.isPrettyPrintMultiLine();
    cond.prettyPrint(builder);
    builder.print(", ");
    if (multiLine) builder.println();

    multiLine = operand1.isPrettyPrintMultiLine();
    if (multiLine) builder.println();
    operand1.prettyPrint(builder);
    builder.print(", ");
    if (multiLine) builder.println();

    multiLine = operand2.isPrettyPrintMultiLine();
    if (multiLine) builder.println();
    operand2.prettyPrint(builder);
    if (multiLine) builder.println();

    builder.indent(-4).print(")");
  }

  @Override
  protected boolean isPrettyPrintMultiLine() {
    return cond.isPrettyPrintMultiLine()
            || operand1.isPrettyPrintMultiLine()
            || operand2.isPrettyPrintMultiLine();
  }

  @Override
  public boolean isLia() {
    return true;
  }

  @Override
  public LiaOpType getType() {
    return LiaOpType.LITE;
  }

  @Override
  public Set<String> getVars() {
    Set<String> result = operand1.getVars();
    result.addAll(operand2.getVars());
    result.addAll(cond.getVars());
    return result;
  }

  @Override
  public Liastar deepcopy() {
    return mkIte(innerStar, cond.deepcopy(), operand1.deepcopy(), operand2.deepcopy());
  }

  @Override
  public Liastar mergeMult(HashMap<LiamultImpl, String> multToVar) {
    cond = cond.mergeMult(multToVar);
    operand1 = operand1.mergeMult(multToVar);
    operand2 = operand2.mergeMult(multToVar);
    return this;
  }


  @Override
  public Liastar multToBin(int n) {
    cond = cond.multToBin(n);
    operand1 = operand1.multToBin(n);
    operand2 = operand2.multToBin(n);
    return this;
  }

  @Override
  public boolean equals(Object that) {
    if(that == this)
      return true;
    if(that == null)
      return false;
    if(!(that instanceof LiaiteImpl))
      return false;
    LiaiteImpl tmp = (LiaiteImpl) that;
    return cond.equals(tmp.cond) && operand1.equals(tmp.operand1) && operand2.equals(tmp.operand2);
  }

  @Override
  public int hashCode() {
    return operand1.hashCode();
  }

  @Override
  public Liastar simplifyMult(HashMap<Liastar, String> multToVar) {
    cond.innerStar = innerStar;
    operand1.innerStar = innerStar;
    operand2.innerStar = innerStar;

    Liastar[] tmp = new Liastar[3];
    tmp[0] = cond.simplifyMult(multToVar);
    tmp[1] = operand1.simplifyMult(multToVar);
    tmp[2] = operand2.simplifyMult(multToVar);

    return liaAndConcat(tmp);
  }

  public boolean binIte() {
    if( operand1.getType().equals(LiaOpType.LCONST) &&
        operand2.getType().equals(LiaOpType.LCONST) ) {
      LiaconstImpl c1 = (LiaconstImpl) operand1;
      LiaconstImpl c2 = (LiaconstImpl) operand2;
      if( c1.getValue() <= 1 && c2.getValue() <= 1)
        return true;
      else
        return false;
    }
    return false;
  }

  @Override
  public Liastar expandStar() throws Exception {
    return this;
  }

  @Override
  public Expr transToSMT(Context ctx, HashMap<String, IntExpr> varsName) {
    BoolExpr f = (BoolExpr) cond.transToSMT(ctx, varsName);
    Expr one = operand1.transToSMT(ctx, varsName);
    Expr two = operand2.transToSMT(ctx, varsName);
    return ctx.mkITE(f, one, two);
  }

  static Liastar multIteOneOp(boolean innerStar, Liastar operand, Liastar f) {
    if(operand.isConstV(1)) {
      return f.deepcopy();
    } else if(operand instanceof LiaiteImpl) {
      return ((LiaiteImpl) operand).MultIte(f);
    } else if(f instanceof LiaiteImpl) {
      return ((LiaiteImpl) f.deepcopy()).MultIte(operand);
    } else if(!operand.isConstV(0)){
      return mkMult(innerStar, operand, f).deepcopy();
    } else {
      return operand.deepcopy();
    }
  }

  public Liastar MultIte(Liastar f) {
    if(f.isConstV(1)) {
      return this;
    } else if(f.isConstV(0)) {
      return f.deepcopy();
    }

    if(f instanceof LiaiteImpl) {
      LiaiteImpl fIte = (LiaiteImpl) f;
      if(fIte.cond.equals(cond)) {
        operand1 = multIteOneOp(innerStar, operand1, fIte.operand1);
        operand2 = multIteOneOp(innerStar, operand2, fIte.operand2);
        return this;
      }
    }

    operand1 = multIteOneOp(innerStar, operand1, f);
    operand2 = multIteOneOp(innerStar, operand2, f);

    return this;
  }

  static Liastar plusIteOneOp(boolean innerStar, Liastar operand, Liastar f) {
    if(operand instanceof LiaiteImpl) {
      return ((LiaiteImpl) operand).plusIte(f);
    } else if(f instanceof LiaiteImpl) {
      return ((LiaiteImpl) f.deepcopy()).plusIte(operand);
    } else {
      return mkPlus(innerStar, operand, f).deepcopy();
    }
  }

  public Liastar plusIte(Liastar f) {
    if(f.isConstV(0)) {
      return this;
    }

    if(f instanceof LiaiteImpl) {
      LiaiteImpl fIte = (LiaiteImpl) f;
      if(fIte.cond.equals(cond)) {
        Liastar fop1 = fIte.operand1;
        Liastar fop2 = fIte.operand2;
        operand1 = plusIteOneOp(innerStar, operand1, fop1);
        operand2 = plusIteOneOp(innerStar, operand2, fop2);
        return this;
      }
    }
    operand1 = plusIteOneOp(innerStar, operand1, f);
    operand2 = plusIteOneOp(innerStar, operand2, f);
    return this;
  }

  @Override
  public EstimateResult estimate() {
    EstimateResult rc = cond.estimate();
    EstimateResult rn = Liastar.mkNot(innerStar, cond).estimate();
    EstimateResult r1 = operand1.estimate();
    EstimateResult r2 = operand2.estimate();
    rc.vars.addAll(r1.vars);
    rc.vars.addAll(r2.vars);
    return new EstimateResult(
            rc.vars,
            Math.max(rc.n_extra + r1.n_extra, rn.n_extra + r2.n_extra),
            Math.max(rc.m + r1.m, rn.m + r2.m),
            Math.max(Math.max(rc.a, rn.a), Math.max(r1.a, r2.a))
    );
  }

  @Override
  public Expr expandStarWithK(Context ctx, Solver sol, String suffix) {
    return ctx.mkITE(
            (BoolExpr)cond.expandStarWithK(ctx, sol, suffix),
            operand1.expandStarWithK(ctx, sol, suffix),
            operand2.expandStarWithK(ctx, sol, suffix)
    );
  }

  @Override
  public Liastar simplifyIte() {
    cond = cond.simplifyIte();
    operand1 = operand1.simplifyIte();
    operand2 = operand2.simplifyIte();
    if(operand1.equals(operand2)) {
      return operand1.deepcopy();
    }
    if(isTrue(cond)) {
      return operand1.deepcopy();
    }
    else if(isFalse(cond)) {
      return operand2.deepcopy();
    }
    return this;
  }

  @Override
  public int embeddingLayers() {
    return cond.embeddingLayers();
  }

  @Override
  public Liastar transformPostOrder(Function<Liastar, Liastar> transformer) {
    Liastar cond0 = cond.transformPostOrder(transformer);
    Liastar operand10 = operand1.transformPostOrder(transformer);
    Liastar operand20 = operand2.transformPostOrder(transformer);
    return transformer.apply(mkIte(innerStar, cond0, operand10, operand20));
  }

}


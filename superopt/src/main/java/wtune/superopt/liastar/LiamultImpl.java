package wtune.superopt.liastar;

import com.microsoft.z3.*;
import wtune.superopt.util.PrettyBuilder;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

public class LiamultImpl extends Liastar {

  Liastar operand1;
  Liastar operand2;

  LiamultImpl(Liastar op1, Liastar op2) {
    operand1 = op1;
    operand2 = op2;
  }

  @Override
  public Liastar expandStar() throws Exception {
    return this;
  }

  @Override
  protected void prettyPrint(PrettyBuilder builder) {
    boolean needsParen1 = (operand1 instanceof LiaplusImpl);
    boolean needsParen2 = (operand1 instanceof LiaplusImpl);
    prettyPrintBinaryOp(builder, operand1, operand2,
            needsParen1, needsParen2, " x ");
  }

  @Override
  protected boolean isPrettyPrintMultiLine() {
    return operand1.isPrettyPrintMultiLine()
            || operand2.isPrettyPrintMultiLine();
  }

  @Override
  public boolean isLia() {
    return true;
  }

  @Override
  public LiaOpType getType() {
    return LiaOpType.LMULT;
  }

  @Override
  public Set<String> getVars() {
    Set<String> result = operand1.getVars();
    result.addAll(operand2.getVars());
    return result;
  }

  @Override
  public Liastar deepcopy() {
    return mkMult(innerStar, operand1.deepcopy(), operand2.deepcopy());
  }

  @Override
  public boolean equals(Object obj) {
    if(obj == null)
      return false;
    if(!(obj instanceof LiamultImpl))
      return false;
    if(obj == this)
      return true;
    LiamultImpl that = (LiamultImpl) obj;
    HashSet<Liastar> thisItems = new HashSet<>();
    HashSet<Liastar> thatItems = new HashSet<>();
    decomposeMults(this, thisItems);
    decomposeMults(that, thatItems);
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
    decomposeMults(this, thisItems);
    int result = 0;
    for(Liastar formula : thisItems) {
      result = result + formula.hashCode();
    }
    return result;
  }

  @Override
  public Liastar mergeMult(HashMap<LiamultImpl, String> multToVar) {
    if(innerStar == false)
      return this;
    for(LiamultImpl cur : multToVar.keySet()) {
      if(this.equals(cur))
        return mkVar(true, multToVar.get(cur));
    }
    String newName = newVarName();
    multToVar.put(this, newName);
    return mkVar(true, newName);
  }


  @Override
  public Liastar multToBin(int n) {
    return this;
//    if(innerStar == false)
//      return this;
//
//    Set<String> varSet = collectVarSet();
//    ArrayList<String> array = new ArrayList<>();
//    array.addAll(varSet);
//    return transMult(n, array, 0);
  }

  boolean isSimp(Liastar l) {
    LiaOpType type = l.getType();
    return type.equals(LiaOpType.LMULT) ||
           type.equals(LiaOpType.LVAR)  ||
           type.equals(LiaOpType.LCONST);
  }

  Liastar transMult(int nbits, ArrayList<String> varSet, int start) {
    assert start < varSet.size();

    if(start == (varSet.size() - 1))
      return mkVar(true, varSet.get(start));

    Liastar exp = transMult(nbits, varSet, start + 1);
    String baseName = varSet.get(start);
    Liastar result = null;
    for(int i = 0; i < nbits; i = i + 1) {
      String bitName = baseName + "_" + i;
      if(result == null) {
        result = mkIte(true, mkEq(true, mkVar(true, bitName), mkConst(true, 0)),
            mkConst(true, 0), exp );
      } else {
        Liastar tmp = exp;
        for(int j = 1; j < (1 << i); j = j + 1) {
          tmp = mkPlus(true, exp, tmp);
        }
        result = mkPlus(true, result,
            mkIte( true,
                mkEq(true, mkVar(true, bitName), mkConst(true, 0)),
                mkConst(true, 0), tmp)
        );
      }
    }
    return result;
  }

  @Override
  public Set<String> collectVarSet() {
    Set<String> varSet = operand1.collectVarSet();
    varSet.addAll(operand2.collectVarSet());
    return varSet;
  }

  @Override
  public Liastar simplifyMult(HashMap<Liastar, String> multToVar) {
    operand1.innerStar = innerStar;
    operand2.innerStar = innerStar;
    Liastar[] starArray = new Liastar[4];
    starArray[0] = operand1.simplifyMult(multToVar);
    starArray[1] = operand2.simplifyMult(multToVar);
    starArray[2] = null;
    starArray[3] = null;

    if(innerStar) {
      if (!isSimp(operand1)) {
        String tmpName = null;
        if(multToVar.containsKey(operand1))
          tmpName = multToVar.get(operand1);
        else
          tmpName = newVarName();
        multToVar.put(operand1, tmpName);

        starArray[2] = mkEq(true, mkVar(true, tmpName), operand1);
        operand1 = mkVar(true, tmpName);
      }
      if (!isSimp(operand2)) {
        String tmpName = null;
        if(multToVar.containsKey(operand2))
          tmpName = multToVar.get(operand2);
        else
          tmpName = newVarName();
        multToVar.put(operand2, tmpName);

        starArray[3] = mkEq(true, mkVar(true, tmpName), operand2);
        operand2 = mkVar(true, tmpName);
      }
      return liaAndConcat(starArray);
    } else {
      return null;
    }
  }


  @Override
  public Expr transToSMT(Context ctx, HashMap<String, IntExpr> varsName) {
    ArithExpr one = (ArithExpr) operand1.transToSMT(ctx, varsName);
    ArithExpr two = (ArithExpr) operand2.transToSMT(ctx, varsName);
    return ctx.mkMul(one, two);
  }

  @Override
  public EstimateResult estimate() {
    throw new RuntimeException("Can not estimate for multiplication. Please expand all the multiplication inside stars before calling `expandStarWithK`");
  }

  @Override
  public Expr expandStarWithK(Context ctx, Solver sol, String suffix) {
    return ctx.mkMul(
      (ArithExpr)operand1.expandStarWithK(ctx, sol, suffix),
      (ArithExpr)operand2.expandStarWithK(ctx, sol, suffix)
    );
  }

  @Override
  public Liastar simplifyIte() {
    operand1 = operand1.simplifyIte();
    operand2 = operand2.simplifyIte();
    Liastar tmpZero = mkConst(innerStar, 0);
    Liastar tmpOne = mkConst(innerStar, 1);
    if(operand1.equals(tmpZero) || operand2.equals(tmpZero)) {
      return tmpZero.deepcopy();
    }
    if(operand1.equals(tmpOne)) {
      return operand2;
    }
    if(operand2.equals(tmpOne)) {
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
    return transformer.apply(mkMult(innerStar, operand10, operand20));
  }

}

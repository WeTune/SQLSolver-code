package wtune.superopt.uexpr;

import java.util.HashSet;
import java.util.Set;

import static wtune.common.utils.IterableSupport.all;
import static wtune.superopt.uexpr.UVar.VarKind.BASE;

public interface USum extends UUnary {
  @Override
  default UKind kind() {
    return UKind.SUMMATION;
  }

  Set<UVar> boundedVars();

  boolean isUsingBoundedVar(UVar var);

  boolean removeBoundedVar(UVar var);

  boolean removeBoundedVarForce(UVar vat);

  void removeUnusedBoundedVar();

  static USum mk(Set<UVar> sumVars, UTerm body) {
    assert all(sumVars, it -> it.kind() == BASE);

    if (body.kind().isBinary()) return new USumImpl(sumVars, body);
    else return new USumImpl(sumVars, UMul.mk(body));
  }

  public UTerm replaceTerm(UTerm baseTerm, UTerm repTerm);

  public UTerm addMulSubTerm(UTerm newTerm);

  public boolean addBoundedVarForce(UVar var);

  Set<String> getBoundVarNames();

}

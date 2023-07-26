package wtune.superopt.uexpr;

import java.util.List;

import static wtune.superopt.uexpr.UExprSupport.transformTerms;

record UNegImpl(UTerm body) implements UNeg {
  @Override
  public boolean isUsing(UVar var) {
    return body.isUsing(var);
  }

  @Override
  public boolean isUsingProjVar(UVar var) {
    return body.isUsingProjVar(var);
  }

  @Override
  public UTerm replaceVar(UVar baseVar, UVar repVar, boolean freshVar) {
    final UTerm e = body.replaceVar(baseVar, repVar, freshVar);
    return UNeg.mk(e);
  }

  @Override
  public boolean replaceVarInplace(UVar baseVar, UVar repVar, boolean freshVar) {
    return body.replaceVarInplace(baseVar, repVar, freshVar);
  }

  @Override
  public boolean replaceVarInplaceWOPredicate(UVar baseVar, UVar repVar) {
    return body.replaceVarInplaceWOPredicate(baseVar, repVar);
  }

  @Override
  public UTerm replaceAtomicTerm(UTerm baseTerm, UTerm repTerm) {
    assert baseTerm.kind().isTermAtomic();
    final UTerm replaced = body.replaceAtomicTerm(baseTerm, repTerm);
    return new UNegImpl(replaced);
  }

  @Override
  public UTerm copy() {
    final UTerm copyBody = body.copy();
    return new UNegImpl(copyBody);
  }

  @Override
  public String toString() {
    return "not(" + body + ")";
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (!(obj instanceof UNeg)) return false;

    final UNeg that = (UNeg) obj;
    return this.body.equals(that.body());
  }

  @Override
  public int hashCode() {
    return body.hashCode();
  }
}

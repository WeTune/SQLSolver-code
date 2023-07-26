package wtune.superopt.uexpr;

record USquashImpl(UTerm body) implements USquash {
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
    return USquash.mk(e);
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
    return new USquashImpl(replaced);
  }

  @Override
  public UTerm copy() {
    final UTerm copyBody = body.copy();
    return new USquashImpl(copyBody);
  }

  @Override
  public String toString() {
    return "||" + body + "||";
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (!(obj instanceof USquash)) return false;

    final USquash that = (USquash) obj;
    return this.body.equals(that.body());
  }

  @Override
  public int hashCode() {
    return body.hashCode();
  }
}

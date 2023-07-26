package wtune.superopt.uexpr;

final class ULiaVarImpl implements ULiaVar {
  private UVar var;

  ULiaVarImpl(UVar var) {
    this.var = var;
  }

  @Override
  public UVar var() {
    return var;
  }

  @Override
  public boolean isUsing(UVar var) {
    return this.var.isUsing(var);
  }

  @Override
  public boolean isUsingProjVar(UVar var) {
    return this.var.isUsingProjVar(var);
  }

  @Override
  public UTerm replaceVar(UVar baseVar, UVar repVar, boolean freshVar) {
    final UVar v = var.replaceVar(baseVar, repVar);
    return ULiaVar.mk(v);
  }

  @Override
  public boolean replaceVarInplace(UVar baseVar, UVar repVar, boolean freshVar) {
    final UVar newVar = var.replaceVarInplace(baseVar, repVar);
    if (!newVar.equals(var)) {
      var = newVar;
      return true;
    }
    return false;
  }

  @Override
  public boolean replaceVarInplaceWOPredicate(UVar baseVar, UVar repVar) {
    final UVar newVar = var.replaceVarInplace(baseVar, repVar);
    if (!newVar.equals(var)) {
      var = newVar;
      return true;
    }
    return false;
  }

  @Override
  public UTerm replaceAtomicTerm(UTerm baseTerm, UTerm repTerm) {
    assert baseTerm.kind().isTermAtomic();
    if (this.equals(baseTerm)) return repTerm.copy();
    return this.copy();
  }

  @Override
  public UTerm copy() {
    return new ULiaVarImpl(var.copy());
  }

  @Override
  public String toString() {
    return var.toString();
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (!(obj instanceof ULiaVar)) return false;

    final ULiaVar that = (ULiaVar) obj;
    return this.var.equals(that.var());
  }

  @Override
  public int hashCode() {
    return var.hashCode();
  }
}

package wtune.superopt.uexpr;

final class UConstImpl implements UConst {

  private final int value;

  private UConstImpl(int value) {
    this.value = value;
  }

  static UConst mkVal(int v) {
    return new UConstImpl(v);
  }

  static UConst mkNull() {
    return new UConstImpl(Integer.MIN_VALUE);
  }

  @Override
  public int value() {
    return value;
  }

  @Override
  public boolean isZeroOneVal() {
    return value == 0 || value == 1;
  }

  @Override
  public boolean replaceVarInplaceWOPredicate(UVar baseVar, UVar repVar) {
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
    return new UConstImpl(value);
  }

  @Override
  public String toString() {
    return String.valueOf(value);
  }

  @Override
  public boolean equals(Object obj) {
    if (obj == this) return true;
    if (!(obj instanceof UConst)) return false;

    final UConst that = (UConst) obj;
    return that.value() == this.value;
  }

  @Override
  public int hashCode() {
    return Integer.hashCode(value);
  }
}

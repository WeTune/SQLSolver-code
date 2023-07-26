package wtune.superopt.uexpr;

import java.util.Objects;

public class UStringImpl implements UString {

  private final String value;

  private UStringImpl(String value) {
        this.value = value;
    }

  static UString mkVal(String v) {
        return new UStringImpl(v);
    }
  static UString mkNull() {
        return new UStringImpl("");
    }

  @Override
  public String value() {
        return value;
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
        return new UStringImpl(value);
    }

  @Override
  public String toString() {
        return "'" + String.valueOf(value) + "'";
    }

  @Override
  public boolean equals(Object obj) {
    if (obj == this) return true;
    if (!(obj instanceof UString)) return false;

    final UString that = (UString) obj;
    return Objects.equals(that.value(), this.value);
  }

  @Override
  public int hashCode() {
        return value.hashCode();
    }
}

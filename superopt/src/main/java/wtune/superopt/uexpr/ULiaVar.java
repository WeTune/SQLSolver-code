package wtune.superopt.uexpr;

public interface ULiaVar extends UAtom {
  @Override
  default UKind kind() {
    return UKind.PRED;
  }

  static ULiaVar mk(UVar var) {
    return new ULiaVarImpl(var);
  }

  static ULiaVar mk(String name) {
    return new ULiaVarImpl(UVar.mkBase(UName.mk(name)));
  }
}

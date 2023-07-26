package wtune.superopt.fragment;

public interface Union extends SetOp {
  @Override
  default OpKind kind() {
    return OpKind.UNION;
  }
}

package wtune.sql.plan;

final public class ValueImpl implements Value {
  private final int id;
  private String qualification;
  private final String name;

  public ValueImpl(int id, String qualification, String name) {
    this.id = id;
    this.qualification = qualification;
    this.name = name;
  }

  @Override
  public int id() {
    return id;
  }

  @Override
  public String name() {
    return name;
  }

  @Override
  public String qualification() {
    return qualification;
  }

  @Override
  public void setQualification(String qualification) {
    this.qualification = qualification;
  }

  @Override
  public boolean equals(Object obj) {
    if (obj == this) return true;
    if (!(obj instanceof Value)) return false;
    return this.id() == ((Value) obj).id();
  }

  @Override
  public int hashCode() {
    return Integer.hashCode(id);
  }

  @Override
  public String toString() {
    return qualification + "." + name;
  }
}

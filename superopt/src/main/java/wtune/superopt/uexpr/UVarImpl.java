package wtune.superopt.uexpr;

import java.util.Arrays;

import static java.util.Arrays.asList;
import static wtune.common.utils.Commons.joining;
import static wtune.common.utils.IterableSupport.any;

record UVarImpl(VarKind kind, UName name, UVar[] arguments) implements UVar {

  @Override
  public boolean isUsing(UVar var) {
    // assert var.is(VarKind.BASE);
    if (!var.is(VarKind.BASE)) return false;
    if (this.is(VarKind.BASE)) return this.equals(var);
    else return any(asList(arguments), it -> it.isUsing(var));
  }

  @Override
  public boolean isUsingProjVar(UVar var) {
    if (!var.is(VarKind.PROJ)) return false;
    if(this.is(VarKind.PROJ)) return this.equals(var);
    else if(this.is(VarKind.CONCAT)) return any(asList(arguments), it -> it.isUsingProjVar(var));
    else return false;
  }

  @Override
  public UVar replaceVar(UVar baseVar, UVar repVar) {
    // Only support replacing var of `BASE` and `PROJ` kind
    // assert baseVar.isUnaryVar() && repVar.isUnaryVar();
    if (this.is(VarKind.BASE)) return this.equals(baseVar) ? repVar.copy() : this.copy();
    if (this.is(VarKind.PROJ) && this.equals(baseVar)) return repVar.copy();
    if (this.is(VarKind.CONCAT) && this.equals(baseVar)) return repVar.copy();

    UVar[] newVars = Arrays.copyOf(arguments, arguments.length);
    for (int i = 0, bound = arguments.length; i < bound; i++) {
      final UVar v = arguments[i].replaceVar(baseVar, repVar);
      newVars[i] = v;
    }
    return new UVarImpl(kind, name, newVars);
  }

  @Override
  public UVar replaceVarInplace(UVar baseVar, UVar repVar) {
    // Also make its return type to be `UVar` for cases of whole replacement of UVar
    // assert baseVar.isUnaryVar() && repVar.isUnaryVar();
    if (this.is(VarKind.BASE)) return this.equals(baseVar) ? repVar.copy() : this.copy();
    if (this.is(VarKind.PROJ) && this.equals(baseVar)) return repVar.copy();
    if (this.is(VarKind.CONCAT) && this.equals(baseVar)) return repVar.copy();

    UVar[] newVars = Arrays.copyOf(arguments, arguments.length);
    for (int i = 0, bound = arguments.length; i < bound; i++) {
      final UVar v = arguments[i].replaceVar(baseVar, repVar);
      newVars[i] = v;
    }
    return new UVarImpl(kind, name, newVars);
  }

  @Override
  public UVar[] args() {
    return arguments;
  }

  @Override
  public UVar copy() {
    if (is(VarKind.BASE)) return UVar.mkBase(name.copy());

    final UVar[] copyArgs = new UVar[arguments.length];
    for (int i = 0, bound = arguments.length; i < bound; ++i) {
      copyArgs[i] = arguments[i].copy();
    }
    return new UVarImpl(kind, name.copy(), copyArgs);
  }

  @Override
  public String toString() {
    if (kind == VarKind.BASE) return name.toString();

    final StringBuilder builder = new StringBuilder(name.toString());
    return joining("(", ",", ")", false, asList(arguments), builder).toString();
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (!(obj instanceof UVar)) return false;
    final UVar that = (UVar) obj;
    if (this.kind != that.kind()) return false;

    if (this.is(VarKind.BASE)) return this.name.equals(that.name());
    else {
      if (!this.name.equals(that.name()) || this.args().length != that.args().length) return false;
      for (int i = 0, bound = this.args().length; i < bound; ++i) {
        if (!this.args()[i].equals(that.args()[i])) return false;
      }
      return true;
    }
  }

  @Override
  public int hashCode() {
    if (kind == VarKind.BASE) return name.hashCode();
    return name.hashCode() * 31 + Arrays.hashCode(arguments);
  }
}

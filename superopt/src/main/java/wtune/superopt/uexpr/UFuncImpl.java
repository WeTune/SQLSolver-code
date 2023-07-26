package wtune.superopt.uexpr;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import static wtune.common.utils.IterableSupport.any;
import static wtune.superopt.uexpr.UExprSupport.transformTerms;

public class UFuncImpl implements UFunc {
  private FuncKind funcKind;
  private UName funcName;
  private final List<UTerm> arguments;

  public UFuncImpl(FuncKind funcKind, UName funcName, List<UTerm> arguments) {
    this.funcKind = funcKind;
    this.funcName = funcName;
    this.arguments = arguments;
  }

  @Override
  public List<UTerm> subTerms() {
        return arguments;
    }

  @Override
  public FuncKind funcKind() {
        return funcKind;
    }

  @Override
  public UName funcName() {
        return funcName;
    }

  @Override
  public List<UTerm> args() {
        return arguments;
    }

  @Override
  public boolean isUsing(UVar var) {
        return any(arguments, arg -> arg.isUsing(var));
    }

  @Override
  public boolean isUsingProjVar(UVar var) {
        return any(arguments, arg -> arg.isUsingProjVar(var));
    }

  @Override
  public UTerm replaceVar(UVar baseVar, UVar repVar, boolean freshVar) {
    final List<UTerm> replaced = transformTerms(arguments, t -> t.replaceVar(baseVar, repVar, freshVar));
    return UFunc.mk(funcKind, funcName, replaced);
  }

  @Override
  public boolean replaceVarInplace(UVar baseVar, UVar repVar, boolean freshVar) {
    boolean modified = false;
    for (UTerm arg : arguments) {
      if (arg.replaceVarInplace(baseVar, repVar, freshVar)) modified = true;
    }
      return modified;
  }

  @Override
  public boolean replaceVarInplaceWOPredicate(UVar baseVar, UVar repVar) {
    boolean modified = false;
    for (UTerm arg : arguments) {
      if (arg.replaceVarInplaceWOPredicate(baseVar, repVar)) modified = true;
    }
    return modified;
  }

  @Override
  public UTerm replaceAtomicTerm(UTerm baseTerm, UTerm repTerm) {
    assert baseTerm.kind().isTermAtomic();
    if (this.equals(baseTerm)) return repTerm.copy();
    final List<UTerm> replaced = transformTerms(arguments, t -> t.replaceAtomicTerm(baseTerm, repTerm));
    return UFunc.mk(funcKind, funcName, replaced);
  }

  @Override
  public UTerm copy() {
    List<UTerm> copies = new ArrayList<>(arguments);
    for (int i = 0, bound = arguments.size(); i < bound; i++) {
      final UTerm copiedFactor = arguments.get(i).copy();
      copies.set(i, copiedFactor);
    }
    return UFunc.mk(funcKind, funcName.copy(), copies);
  }

  @Override
  public String toString() {
    final StringBuilder builder = new StringBuilder(arguments.size() * 5);
    builder.append(funcName);
    builder.append("(");
    for(int i = 0; i < arguments.size(); i++) {
      if(i == arguments.size() - 1) {
        builder.append(arguments.get(i));
      } else {
        builder.append(arguments.get(i)).append(", ");
      }
    }
    builder.append(")");
    return builder.toString();
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (!(obj instanceof UFunc)) return false;

    UFunc that = (UFunc) obj;
    if (funcKind != that.funcKind() || !funcName.equals(that.funcName())) return false;
    if(arguments.size() != that.args().size()) return false;

    assert arguments.size() == that.args().size();
    return arguments.equals(that.args());
  }

  @Override
  public int hashCode() {
    return funcKind.hashCode() * 31 * 31 + funcName.hashCode() * 31 + new HashSet<>(arguments).hashCode();
  }
}

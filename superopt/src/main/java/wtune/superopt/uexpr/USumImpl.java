package wtune.superopt.uexpr;

import wtune.common.utils.ListSupport;
import wtune.superopt.liastar.Liastar;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static wtune.common.utils.Commons.joining;

record USumImpl(Set<UVar> boundedVars, UTerm body) implements USum {
  @Override
  public boolean isUsing(UVar var) {
    if (!var.is(UVar.VarKind.BASE)) return false;
    return !boundedVars.contains(var) && body.isUsing(var);
  }

  @Override
  public boolean isUsingProjVar(UVar var) {
    if(!var.is(UVar.VarKind.PROJ))  return false;
    return body.isUsingProjVar(var);
  }

  @Override
  public boolean isUsingBoundedVar(UVar var) {
    if (!var.is(UVar.VarKind.BASE)) return false;
    return boundedVars.contains(var);
  }

  @Override
  public UTerm replaceVar(UVar baseVar, UVar repVar, boolean freshVar) {
    // assert baseVar.isUnaryVar() && repVar.isUnaryVar();
    if (freshVar) {
      // Replace a var with a fresh var, `baseVar` and `repVar` should be base var
      assert baseVar.is(UVar.VarKind.BASE) && repVar.is(UVar.VarKind.BASE);
      final UTerm newBody = body.replaceVar(baseVar, repVar, freshVar);
      final Set<UVar> newBoundedVars = new HashSet<>(boundedVars);
      if (isUsingBoundedVar(baseVar)) {
        newBoundedVars.remove(baseVar);
        newBoundedVars.add(repVar);
      }
      return USum.mk(newBoundedVars, newBody);
    } else {
      // Replace a var with an existing known var, `repVar` is either an outer var or using existing bounded vars
      // So do not consider adding `repVar` to boundedVars
      final UTerm newBody = body.replaceVar(baseVar, repVar, freshVar);
      final Set<UVar> newBoundedVars = new HashSet<>(boundedVars);
      return USum.mk(newBoundedVars, newBody);
    }
  }

  @Override
  public boolean replaceVarInplace(UVar baseVar, UVar repVar, boolean freshVar) {
    // assert baseVar.isUnaryVar() && repVar.isUnaryVar();
    if (freshVar) {
      // Replace a var with an existing known var, `repVar` is either an outer var or using existing bounded vars
      // So do not consider adding `repVar` to boundedVars
      assert baseVar.is(UVar.VarKind.BASE) && repVar.is(UVar.VarKind.BASE);
      boolean modified = body.replaceVarInplace(baseVar, repVar, freshVar);
      if (isUsingBoundedVar(baseVar)) {
        boundedVars.remove(baseVar);
        boundedVars.add(repVar);
        modified = true;
      }
      return modified;
    } else {
      // Replace a var with an existing known var, then do not consider adding `repVar` to boundedVars
      return body.replaceVarInplace(baseVar, repVar, freshVar);
    }
  }

  @Override
  public boolean replaceVarInplaceWOPredicate(UVar baseVar, UVar repVar) {
    // assert baseVar.isUnaryVar() && repVar.isUnaryVar();
    // Replace a var with an existing known var, then do not consider adding `repVar` to boundedVars
    return body.replaceVarInplaceWOPredicate(baseVar, repVar);
  }

  @Override
  public UTerm replaceAtomicTerm(UTerm baseTerm, UTerm repTerm) {
    assert baseTerm.kind().isTermAtomic();
    final UTerm replaced = body.replaceAtomicTerm(baseTerm, repTerm);
    final Set<UVar> newBoundedVars = new HashSet<>(boundedVars);
    final USum newSum = USum.mk(newBoundedVars, replaced);
    newSum.removeUnusedBoundedVar();
    return newSum;
  }

  public UTerm replaceTerm(UTerm baseTerm, UTerm repTerm) {
    if (body instanceof UMul) {
      final UTerm replaced = ((UMul) body).replaceTerm(baseTerm, repTerm);
      final Set<UVar> newBoundedVars = new HashSet<>(boundedVars);
      final USum newSum = USum.mk(newBoundedVars, replaced);
      newSum.removeUnusedBoundedVar();
      return newSum;
    } else {
      return this;
    }
  }

  public UTerm addMulSubTerm(UTerm newTerm) {
    if (body instanceof UMul) {
      ((UMul) body).addFactor(newTerm);
    } else {
      assert false;
    }
    return this;
  }

  @Override
  public boolean removeBoundedVar(UVar var) {
    if (body.isUsing(var)) return false;
    return boundedVars().remove(var);
  }

  public boolean removeBoundedVarForce(UVar var) {
    return boundedVars().remove(var);
  }

  public boolean addBoundedVarForce(UVar var) {
    return boundedVars().add(var);
  }

  @Override
  public void removeUnusedBoundedVar() {
    boundedVars.removeIf(v -> !body.isUsing(v));
  }

  @Override
  public UTerm copy() {
    final UTerm copyBody = body.copy();
    return new USumImpl(new HashSet<>(boundedVars), copyBody);
  }

  @Override
  public String toString() {
    final StringBuilder builder = new StringBuilder("\u2211");
    final List<String> vars = ListSupport.map(boundedVars, UVar::toString);
    vars.sort(String::compareTo);
    joining("{", ",", "}", false, vars, builder);
    builder.append('(').append(body).append(')');
    return builder.toString();
  }

  boolean checkSameSum(int cur, List<UVar> boundedVars, UTerm body, HashSet<UVar> thatBoundVars, UTerm thatBody) {
    if (cur == boundedVars.size()) return body.equals(thatBody);

    final UVar curVar = boundedVars.get(cur);
    final UVar newVar = UVar.mkBase(UName.mk(Liastar.newVarName()));
    body = body.replaceVar(curVar, newVar, true);

    for (UVar v: thatBoundVars) {
      final HashSet<UVar> tmpVars = new HashSet<>(thatBoundVars);
      tmpVars.remove(v);
      final UTerm tmpThatBody = thatBody.replaceVar(v, newVar, true);
      final boolean result = checkSameSum(cur + 1, boundedVars, body, tmpVars, tmpThatBody);
      if (result) return true;
    }
    return false;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (!(obj instanceof USum)) return false;
    final USum that = (USum) obj;
    UTerm thatBody = that.body().copy();
    HashSet<UVar> thatBoundVars = new HashSet<>(that.boundedVars());

    if (boundedVars.size() != thatBoundVars.size()) return false;
    if (boundedVars.equals(thatBoundVars) && body.equals(thatBody)) return true;

    return checkSameSum(0, new ArrayList<>(boundedVars), body.copy(), thatBoundVars, thatBody);
  }

  @Override
  public int hashCode() {
    return boundedVars.size() * 31 + body.subTerms().size();
  }
}

package wtune.superopt.uexpr;

import wtune.common.utils.Copyable;

import java.util.List;

import static wtune.common.utils.ListSupport.filter;import static wtune.superopt.uexpr.UKind.VAR;

/** A U-expr. */
public interface UTerm extends Copyable<UTerm> {

  UKind kind();

  List<UTerm> subTerms();

  default List<UTerm> subTermsOfKind(UKind kind) {
    return filter(subTerms(), term -> term.kind() == kind);
  }

  boolean isUsing(UVar var);

  boolean isUsingProjVar(UVar var);

  UTerm replaceVar(UVar baseVar, UVar repVar, boolean freshVar);

  boolean replaceVarInplace(UVar baseVar, UVar repVar, boolean freshVar);


  boolean replaceVarInplaceWOPredicate(UVar baseVar, UVar repVar);

  UTerm replaceAtomicTerm(UTerm baseTerm, UTerm repTerm);

  default boolean tupleProjectedFromFuncParam(UVar outVar) {
    return (kind() == VAR) && isUsing(outVar);
  }

}

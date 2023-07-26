package wtune.superopt.uexpr;

import java.util.*;

import static wtune.common.utils.IterableSupport.any;
import static wtune.superopt.uexpr.UExprSupport.transformTerms;

final class UMulImpl implements UMul {
  private final List<UTerm> factors;

  UMulImpl(List<UTerm> factors) {
    this.factors = factors;
  }

  static UMul mk(UTerm e) {
    final List<UTerm> factors = new ArrayList<>(e.subTerms().size() + 1);
    addFactor(factors, e);
    return new UMulImpl(factors);
  }

  static UMul mk(UTerm e0, UTerm e1) {
    final List<UTerm> factors = new ArrayList<>(e0.subTerms().size() + e1.subTerms().size() + 1);
    addFactor(factors, e0);
    addFactor(factors, e1);
    return new UMulImpl(factors);
  }

  static UMul mk(UTerm e0, UTerm e1, UTerm... others) {
    final int sum = Arrays.stream(others).map(UTerm::subTerms).mapToInt(List::size).sum();
    final List<UTerm> factors =
        new ArrayList<>(e0.subTerms().size() + e1.subTerms().size() + sum + 1);
    addFactor(factors, e0);
    addFactor(factors, e1);
    for (UTerm factor : others) addFactor(factors, factor);
    return new UMulImpl(factors);
  }

  static UMul mk(UTerm e0, List<UTerm> others) {
    int sum = 0;
    for(UTerm e : others)
      sum += e.subTerms().size();
    final List<UTerm> factors =
            new ArrayList<>(e0.subTerms().size() + sum + 1);
    addFactor(factors, e0);
    for (UTerm factor : others) addFactor(factors, factor);
    return new UMulImpl(factors);
  }

  private static void addFactor(List<UTerm> factors, UTerm factor) {
    if (factor.kind() == UKind.MULTIPLY) factors.addAll(factor.subTerms());
    else factors.add(factor);
  }

  @Override
  public List<UTerm> subTerms() {
    return factors;
  }

  @Override
  public boolean isUsing(UVar var) {
    return any(factors, it -> it.isUsing(var));
  }

  @Override
  public boolean isUsingProjVar(UVar var) {
    return any(factors, it -> it.isUsingProjVar(var));
  }

  @Override
  public UTerm replaceVar(UVar baseVar, UVar repVar, boolean freshVar) {
    final List<UTerm> replaced = transformTerms(factors, t -> t.replaceVar(baseVar, repVar, freshVar));
    return new UMulImpl(replaced);
  }

  public void addFactor(UTerm term) {
    factors.add(term);
  }

  @Override
  public boolean replaceVarInplace(UVar baseVar, UVar repVar, boolean freshVar) {
    boolean modified = false;
    for (UTerm factor : factors) {
      if (factor.replaceVarInplace(baseVar, repVar, freshVar)) modified = true;
    }
    return modified;
  }

  @Override
  public boolean replaceVarInplaceWOPredicate(UVar baseVar, UVar repVar) {
    boolean modified = false;
    for (UTerm factor : factors) {
      if (factor.replaceVarInplaceWOPredicate(baseVar, repVar)) modified = true;
    }
    return modified;
  }

  @Override
  public UTerm replaceAtomicTerm(UTerm baseTerm, UTerm repTerm) {
    assert baseTerm.kind().isTermAtomic();
    final List<UTerm> replaced = transformTerms(factors, t -> t.replaceAtomicTerm(baseTerm, repTerm));
    return new UMulImpl(replaced);
  }

  public UTerm replaceTerm(UTerm baseTerm, UTerm repTerm) {
    final List<UTerm> replaced = transformTerms(factors, t -> t.equals(baseTerm) ? repTerm : t);
    return new UMulImpl(replaced);
  }

  @Override
  public UTerm copy() {
    List<UTerm> copies = new ArrayList<>(factors);
    for (int i = 0, bound = factors.size(); i < bound; i++) {
      final UTerm copiedFactor = factors.get(i).copy();
      copies.set(i, copiedFactor);
    }
    return new UMulImpl(copies);
  }

  @Override
  public String toString() {
    if (factors.size() == 0) return "";
    else if (factors.size() == 1) return factors.get(0).toString();
    final StringBuilder builder = new StringBuilder(factors.size() * 4);

    final UTerm first = factors.get(0);
    if (first.kind() == UKind.ADD) builder.append('(');
    builder.append(factors.get(0));
    if (first.kind() == UKind.ADD) builder.append(')');

    for (int i = 1, bound = factors.size(); i < bound; i++) {
      final UTerm term = factors.get(i);
      builder.append(" * ");
      if (term.kind() == UKind.ADD) builder.append('(');
      builder.append(term);
      if (term.kind() == UKind.ADD) builder.append(')');
    }

    return builder.toString();
  }

  private boolean idemTerm(UTerm t) {
    switch(t.kind()) {
      case ADD : return false;
      case VAR : return false;
      case PRED : return true;
      case CONST : return ((UConst)t).isZeroOneVal();
      case TABLE : return false;
      case SQUASH : return true;
      case MULTIPLY : {
        for (UTerm subterm : t.subTerms()) {
          if(!idemTerm(subterm))
            return false;
        }
        return true;
      }
      case NEGATION : return true;
      case SUMMATION : return false;
      default: return false;
    }
  }

  static boolean notIsNullUTerm(UTerm expr) {
    if (expr == null)
      return false;

    if (!(expr instanceof UNeg))
      return false;

    UTerm body = ((UNeg) expr).body();
    if (!(body instanceof UPred))
      return false;

    UPred pred = (UPred) body;
    return pred.isPredKind(UPred.PredKind.FUNC) && pred.predName().equals(UName.NAME_IS_NULL);
  }


  // 1 : term is not(isnull(a(t))) and it is ture inferred by subterms
  // 0 : otherwise
  private static int inferNotNull(UTerm term, List<UTerm> subTerms) {
    if (!notIsNullUTerm(term)) return 0;

    ArrayList<UTerm> eqTuples = new ArrayList<>();
    UTerm tuple = ((UPred) ((UNeg)term).body()).args().get(0);
    eqTuples.add(tuple);
    for (UTerm subTerm : subTerms) {
      if (subTerm.kind() == UKind.PRED) {
        UPred pred = (UPred) subTerm;
        if (pred.isPredKind(UPred.PredKind.EQ)) {
          UTerm tuple1 = pred.args().get(0);
          UTerm tuple2 = pred.args().get(0);
          if (any(eqTuples, t -> t.equals(tuple1)) || any(eqTuples, t -> t.equals(tuple2))) {
            eqTuples.add(tuple1);
            eqTuples.add(tuple2);
          }
        }
      }
    }

    for (UTerm subTerm : subTerms) {
      if (notIsNullUTerm(subTerm)) {
        UTerm innerTuple = ((UPred) ((UNeg)subTerm).body()).args().get(0);
        if (eqTuples.contains(innerTuple))
          return 1;
      }
    }

    return 0;
  }

  @Override
  public boolean equals(Object obj) {
    if (obj == this) return true;
    if (!(obj instanceof UMul)) return false;

    final List<UTerm> thisSubTerms = this.subTerms();
    final List<UTerm> thatSubTerms = ((UMul) obj).subTerms();
    if (thatSubTerms.equals(thisSubTerms)) {
      return true;
    }
    for (UTerm thisTerm : thisSubTerms) {
      if (!thatSubTerms.contains(thisTerm)) {
        return false;
      } else if (idemTerm(thisTerm) == false) {
        if(Collections.frequency(thisSubTerms, thisTerm) != Collections.frequency(thatSubTerms, thisTerm)) {
          return false;
        }
      }
    }
    for (UTerm thatTerm : thatSubTerms) {
      if (!thisSubTerms.contains(thatTerm)) {
        return false;
      }
    }
    return true;
  }

  @Override
  public int hashCode() {
    return new HashSet<>(factors).hashCode();
  }
}

package wtune.superopt.uexpr.normalizer;

import wtune.common.utils.NaturalCongruence;
import wtune.superopt.uexpr.*;

import java.util.*;
import java.util.function.Function;

import static wtune.common.utils.IterableSupport.any;
import static wtune.superopt.uexpr.UExprSupport.transformSubTerms;
import static wtune.superopt.uexpr.UKind.*;

public class UNormalization {
  public boolean isModified;
  public UTerm expr;

  public UNormalization(UTerm expr) {
    this.isModified = false;
    this.expr = expr;
  }

  public static boolean isNormalForm(UTerm expr) {
    return isNormalFormExpr(expr);
  }

  /**
   * Sum-Product Normal Form: E = T1 + .. + Tn, Ti = \sum{t1..tm}([b1] * .. * [bt] * R1(t1) * .. *
   * Rs(ts) * ||E1|| * not(E2)). If m = 0, Ti = [b1] * .. * [bt] * R1(t1) * .. * Rs(ts) * ||E1|| *
   * not(E2). isNormalFormExpr() checks an E, isNormalFormTerm() checks a T.
   */
  private static boolean isNormalFormExpr(UTerm expr) {
    switch (expr.kind()) {
      case ADD:
        for (UTerm subTerm : expr.subTerms()) {
          if (!isNormalFormTerm(subTerm)) return false;
        }
        return true;
      case MULTIPLY: return isNormalFormTerm(expr);
      case SUMMATION: return isNormalFormTerm(((USum) expr).body());
      case SQUASH, NEGATION: return isNormalFormExpr(((UUnary) expr).body());
      case TABLE,PRED:
        // To be considered..., whether we need to consider a single [b] or R(t) to be an E or T?
        // Or wrap them in a UMul() during normalization?
        return true;
      default: return false;
    }
  }

  private static boolean isNormalFormTerm(UTerm term) {
    switch (term.kind()) {
      case MULTIPLY:
        // int squashNum = 0, negNum = 0;
        for (UTerm factor : term.subTerms()) {
          if (factor.kind().isBinary() || factor.kind() == SUMMATION) return false;
          if (factor.kind().isUnary()) {
            // if (factor.kind() == SQUASH) ++squashNum;
            // else ++negNum;
            if (!isNormalFormExpr(((UUnary) factor).body())) return false;
          }
        }
        // return squashNum <= 1 && negNum <= 1;
        return true;
      case SUMMATION:
        final UTerm body = ((USum) term).body();
        if (body.kind() != MULTIPLY) return false;
        return isNormalFormTerm(body);
      case SQUASH, NEGATION: return isNormalFormExpr(((UUnary) term).body());
      case TABLE, PRED: return true;
      default: return false;
    }
  }

  public UTerm normalizeTerm() {
    do {
      isModified = false;
      // A round of normalizations
      expr = performNormalizeRule(this::eliminateSquash);
      expr = performNormalizeRule(this::eliminateNegation);
      expr = performNormalizeRule(this::promoteSummation);
      expr = performNormalizeRule(this::mergeSummation);
//      expr = performNormalizeRule(this::removeSummationSquash);
      expr = performNormalizeRule(this::combineSquash);
      // expr = performNormalizeRule(expr, this::combineNegation);
      expr = performNormalizeRule(this::distributeAddToMul);
      expr = performNormalizeRule(this::distributeAddToSummation);
      expr = performNormalizeRule(this::removeConstants);
      expr = performNormalizeRule(this::constantFolding);
      expr = performNormalizeRule(this::removeSquashClassify);
      expr = performNormalizeRule(this::expandSquashString);
      expr = performNormalizeRule(this::applyReduceFunc);
      expr = performNormalizeRule(this::applyFuncString);
      expr = performNormalizeRule(this::removeRedundantString);
//      expr = performNormalizeRule(this::removeNullMultiplication);
    } while (isModified);

    return expr;
  }

  protected UTerm performNormalizeRule(Function<UTerm, UTerm> transformation) {
    expr = transformation.apply(expr);
    // Routine normalizations
    expr = flatSingletonAddAndMul(expr);
    expr = flatAddAndMul(expr);
    return expr;
  }

  /** ADD/MUL[ E1, .., ADD/MUL[Ei, .., Ej], .., En ] -> ADD/MUL[E1, .., Ei, .., Ej, .., En] * */
  UTerm flatAddAndMul(UTerm expr) {
    expr = transformSubTerms(expr, this::flatAddAndMul);

    final UKind kind = expr.kind();
    if (!kind.isBinary()) return expr;

    final List<UTerm> subTerms = expr.subTerms();
    for (int i = 0, bound = subTerms.size(); i < bound; ++i) {
      final UTerm subTerm = subTerms.get(i);
      if (subTerm.kind() == kind) subTerms.addAll(subTerm.subTerms());
    }

    // This will not remove the flattened sub-terms since the kind of sub-terms must be
    // different from `kind` here, because `flatAddAndMul` starts from the innermost layer
    // of U-expression. e.g. ADD(x1, ADD(ADD(x3, x4), x5), x2) does not exists.
    if (subTerms.removeIf(t -> t.kind() == kind)) isModified = true;
    return expr;
  }

  // /**
  //  * 1. ADD(MUL(E1, .., En)) -> MUL(E1, .., En); MUL(ADD(E1, .., En)) -> ADD(E1, .., En); 2. ADD(E)
  //  * -> MUL(E), where E is not ADD or MUL *
  //  */
  // UTerm flatSingletonAddAndMul(UTerm expr) {
  //   expr = transformSubTerms(expr, this::flatSingletonAddAndMul);
  //
  //   final UKind kind = expr.kind();
  //   if (!kind.isBinary()) return expr;
  //
  //   if (expr.subTerms().size() == 1) {
  //     final UTerm singleSubTerm = expr.subTerms().get(0);
  //     final UKind subTermKind = singleSubTerm.kind();
  //     if (!subTermKind.isBinary()) {
  //       // the singleSubTerm E is not ADD or MUL, then ADD(E) -> MUL(E)
  //       if (kind == ADD) {
  //         expr = UMul.mk(singleSubTerm);
  //         isModified = true;
  //       }
  //       return expr;
  //     }
  //
  //     // expr.kind and singleSubTerm.kind are both MUL and ADD
  //     // then check whether their kinds are different, i.e. ADD(MUL(..)) or MUL(ADD(..))
  //     if (kind != subTermKind) {
  //       expr = singleSubTerm;
  //       isModified = true;
  //     }
  //   }
  //   return expr;
  // }

  /** Remove ADD/MUL with only one element* */
  UTerm flatSingletonAddAndMul(UTerm expr) {
    if (expr.kind() == SUMMATION && ((USum) expr).body().subTerms().size() == 1) {
      // Ignore cases for summation's single-subTerm body (which is always an ADD or MUL)
      UTerm singletonSubTerm = ((USum) expr).body().subTerms().get(0);
      singletonSubTerm = transformSubTerms(singletonSubTerm, this::flatSingletonAddAndMul);
      ((USum) expr).body().subTerms().set(0, singletonSubTerm);
      return expr;
    }
    expr = transformSubTerms(expr, this::flatSingletonAddAndMul);

    final UKind kind = expr.kind();
    if (!kind.isBinary()) return expr;

    if (expr.subTerms().size() == 1) {
      isModified = true;
      return expr.subTerms().get(0);
    }
    return expr;
  }

  /** E * \sum{t}f(t) -> \sum{t}(E * f(t)) * */
  UTerm promoteSummation(UTerm expr) {
    expr = transformSubTerms(expr, this::promoteSummation);
    if (expr.kind() != MULTIPLY) return expr;

    Set<UVar> freeVars = null;
    final ListIterator<UTerm> iter = expr.subTerms().listIterator();
    while (iter.hasNext()) {
      final UTerm factor = iter.next();
      if (factor.kind() == SUMMATION) {
        final USum sum = (USum) factor;
        if (freeVars == null) freeVars = new HashSet<>(sum.boundedVars().size());
        freeVars.addAll(sum.boundedVars());
        iter.set(sum.body());
      }
    }
    if (freeVars != null) {
      isModified = true;
      return USum.mk(freeVars, expr);
    } else return expr;
  }

  /** \sum{x}(f(x) * \sum{y}(g(y))) -> Sum[x,y](f(x)*g(y)) * */
  UTerm mergeSummation(UTerm expr) {
    expr = transformSubTerms(expr, this::mergeSummation);
    if (expr.kind() != SUMMATION) return expr;

    final USum summation = (USum) expr;
    if (summation.body().kind() != MULTIPLY) return expr;

    final Set<UVar> boundedVars = summation.boundedVars();

    // Sum[x](Prod(..,Sum[y](..),..) -> Sum[x,y](..,..,..)
    final List<UTerm> subTerms = summation.body().subTerms();
    for (int i = 0, bound = subTerms.size(); i < bound; i++) {
      final UTerm subTerm = subTerms.get(i);
      if (subTerm.kind() != SUMMATION) continue;

      final USum subSummation = (USum) subTerm;
      boundedVars.addAll(subSummation.boundedVars());
      subTerms.addAll(subSummation.body().subTerms());
      isModified = true;
    }
    subTerms.removeIf(it -> it.kind() == SUMMATION);

    return expr;
  }

  /** ||E1 * ||E|| * E2|| -> ||E1 * E * E2||
   *  not(E1 * ||E|| * E2) -> not(E1 * E * E2) * */
  UTerm eliminateSquash(UTerm expr) {
    return eliminateSquash0(expr, false);
  }

  private UTerm eliminateSquash0(UTerm expr, boolean isActivated) {
    final UKind kind = expr.kind();
    if (isActivated && kind == SQUASH) {
      isModified = true;
      return eliminateSquash0(((USquash) expr).body(), true);
    } else {
      final boolean activated;
      if (kind == PRED) activated = false;
      else activated = isActivated || kind == SQUASH || kind == NEGATION;
      return transformSubTerms(expr, t -> eliminateSquash0(t, activated));
    }
  }

  /** not(not(E)) -> E * */
  UTerm eliminateNegation(UTerm expr) {
    expr = transformSubTerms(expr, this::eliminateNegation);

    final UKind kind = expr.kind();
    if (kind != NEGATION) return expr;

    final UNeg neg = (UNeg) expr;
    if (neg.body().kind() == NEGATION) {
      isModified = true;
      return ((UNeg) neg.body()).body();
    }

    return expr;
  }

  /** ||E1|| * ||E2|| -> ||E1 * E2|| * */
  UTerm combineSquash(UTerm expr) {
    expr = transformSubTerms(expr, this::combineSquash);

    final UKind kind = expr.kind();
    if (kind != MULTIPLY) return expr;

    final List<UTerm> subTerms = expr.subTerms();
    final List<UTerm> squashedTerms = new ArrayList<>();
    for (int i = 0, bound = subTerms.size(); i < bound; ++i) {
      final UTerm subTerm = subTerms.get(i);
      if (subTerm.kind() != SQUASH) continue;
      squashedTerms.add(((USquash) subTerm).body());
    }
    if (squashedTerms.size() > 1) {
      final USquash combinedSquash = USquash.mk(UMul.mk(squashedTerms));
      subTerms.removeIf(t -> t.kind() == SQUASH);
      subTerms.add(combinedSquash);
      isModified = true;
    }

    return expr;
  }

  /** ||\sum{t1}f(t1)|| * ||\sum{t2}(f(t2)*g(t2))|| -> ||\sum{y2}(f(t2)*g(t2))|| * */
  UTerm removeSummationSquash(UTerm expr) {
    expr = transformSubTerms(expr, this::removeSummationSquash);

    final UKind kind = expr.kind();
    if (kind != MULTIPLY) return expr;

    final List<UTerm> subTerms = expr.subTerms();
    final List<UTerm> squashedSummationTerms = new ArrayList<>();
    final Map<UTerm, Boolean> deletedMap = new HashMap<>();
    for (UTerm subTerm : subTerms) {
      deletedMap.put(subTerm, false);
      if (subTerm.kind() != SQUASH) continue;
      if (((USquash) subTerm).body().kind() != SUMMATION) continue;
      squashedSummationTerms.add(subTerm);
    }
    if (squashedSummationTerms.size() > 1) {
      for(int i = 0, bound = squashedSummationTerms.size(); i < bound; ++i) {
        final UTerm firstTerm = squashedSummationTerms.get(i);
        final USum firstSummation = (USum) ((USquash) firstTerm).body();
        if(firstSummation.boundedVars().size() > 1) continue;
        for (int j = i+1; j < bound; ++j) {
          final UTerm secondTerm = squashedSummationTerms.get(j);
          final USum secondSummation = (USum) ((USquash) secondTerm).body();
          if(secondSummation.boundedVars().size() > 1) continue;
          boolean find = false;
          if(containTargetTerm(firstSummation.body(), secondSummation.body(),
                  (UVar) firstSummation.boundedVars().toArray()[0],(UVar) secondSummation.boundedVars().toArray()[0],false)) {
            deletedMap.put(secondTerm, true);
            isModified = true;
            find = true;
          }
          if(find) continue;
          if(containTargetTerm(firstSummation.body(), secondSummation.body(),
                  (UVar) firstSummation.boundedVars().toArray()[0],(UVar) secondSummation.boundedVars().toArray()[0],true)) {
            deletedMap.put(firstTerm, true);
            isModified = true;
          }
        }
      }
      subTerms.removeIf(deletedMap::get);
    }

    return expr;
  }

  private static boolean containTargetTerm(UTerm firstTerm, UTerm secondTerm, UVar firstBoundedVar, UVar secondBoundedVar, boolean firstIsTarget) {
    UTerm srcTerm = firstIsTarget?secondTerm:firstTerm;
    UTerm tgtTerm = firstIsTarget?firstTerm:secondTerm;
    UVar srcBoundedVar = firstIsTarget?secondBoundedVar:firstBoundedVar;
    UVar tgtBoundedVar = firstIsTarget?firstBoundedVar:secondBoundedVar;
    if(srcTerm.kind() == MULTIPLY && tgtTerm.kind() == MULTIPLY) {
      for(UTerm subTgtTerm : tgtTerm.subTerms()) {
        UTerm subTgtTermCopy = subTgtTerm.copy();
        if(subTgtTerm.isUsing(tgtBoundedVar))
          subTgtTermCopy.replaceVarInplace(tgtBoundedVar, srcBoundedVar, false);
        if(!srcTerm.subTerms().contains(subTgtTermCopy)) {
          return false;
        }
      }
      return true;
    }
    if(srcTerm.kind() == MULTIPLY && tgtTerm.kind() != MULTIPLY) {
      UTerm tgtTermCopy = tgtTerm.copy();
      if(tgtTerm.isUsing(tgtBoundedVar))
        tgtTermCopy.replaceVarInplace(tgtBoundedVar, srcBoundedVar, false);
      return srcTerm.subTerms().contains(tgtTermCopy);
    }
    return false;
  }

  private static boolean haveSquash(UTerm term) {
    if(term.kind() == SUMMATION)
        return true;
    for(UTerm subTerm : term.subTerms())
      if(haveSquash(subTerm)) return true;
    return false;
  }

  /** not(E1) * not(E2) -> not(E1 + E2) * */
  UTerm combineNegation(UTerm expr) {
    expr = transformSubTerms(expr, this::combineNegation);

    final UKind kind = expr.kind();
    if (kind != MULTIPLY) return expr;

    final List<UTerm> subTerms = expr.subTerms();
    final List<UTerm> negTerms = new ArrayList<>();
    for (int i = 0, bound = subTerms.size(); i < bound; ++i) {
      final UTerm subTerm = subTerms.get(i);
      if (subTerm.kind() != NEGATION) continue;
      negTerms.add(((UNeg) subTerm).body());
    }
    if (negTerms.size() > 1) {
      final UNeg combinedNeg = UNeg.mk(UAdd.mk(negTerms));
      subTerms.removeIf(t -> t.kind() == NEGATION);
      subTerms.add(combinedNeg);
      isModified = true;
    }

    return expr;
  }

  /** E1 * (E2 + E3) -> E1 * E2 + E1 * E3 */
  UTerm distributeAddToMul(UTerm expr) {
    expr = transformSubTerms(expr, this::distributeAddToMul);

    final UKind kind = expr.kind();
    if (kind != MULTIPLY) return expr;

    final List<UTerm> subTerms = expr.subTerms();
    UAdd subAdd = null;
    for (int i = 0, bound = subTerms.size(); i < bound; ++i) {
      final UTerm subTerm = subTerms.get(i);
      if (subTerm.kind() == ADD) {
        subAdd = (UAdd) subTerm;
        break;
      }
    }

    // Get one of the subTerm to be ADD
    if (subAdd != null) {
      subTerms.remove(subAdd);
      final List<UTerm> addTerms = new ArrayList<>();
      for (int i = 0, bound = subAdd.subTerms().size(); i < bound; ++i) {
        final UTerm subAddFactor = subAdd.subTerms().get(i);
        final List<UTerm> subMulFactors = UExprSupport.copyTermList(subTerms);
        subMulFactors.add(subAddFactor);
        addTerms.add(UMul.mk(subMulFactors));
      }
      expr = UAdd.mk(addTerms);
      isModified = true;
    }

    return expr;
  }

  /**
   * \sum{t} (f1(t) + f2(t)) -> \sum{t}f1(t) + \sum{t}f2(t) Cases like \sum{t} (E1 * (f1(t) + f2(t))
   * * E2) are transformed into \sum{t} (E1 * E2 * f1(t) + E1 * E2 * f2(t)) by `distributeAddToMul`,
   */
  UTerm distributeAddToSummation(UTerm expr) {
    expr = transformSubTerms(expr, this::distributeAddToSummation);

    final UKind kind = expr.kind();
    if (kind != SUMMATION) return expr;

    // Check the pattern: \sum(ADD(.., ..))
    final UTerm body = ((USum) expr).body();
    if (body.kind() == ADD) {
      final List<UTerm> subTerms = body.subTerms();
      final List<UTerm> addFactors = new ArrayList<>();
      for (int i = 0, bound = subTerms.size(); i < bound; ++i) {
        final UTerm subTerm = subTerms.get(i).copy();
        final Set<UVar> usedVars = new HashSet<>();
        for (UVar var : ((USum) expr).boundedVars()) {
          if (subTerm.isUsing(var)) usedVars.add(var);
        }
        addFactors.add(USum.mk(usedVars, subTerm));
      }
      expr = UAdd.mk(addFactors);
      isModified = true;
    }

    return expr;
  }

  /** Remove constants in expression * */
  UTerm removeConstants(UTerm expr) {
    expr = transformSubTerms(expr, this::removeConstants);

    switch (expr.kind()) {
      case ADD -> {
        if (expr.subTerms().removeIf(subTerm -> subTerm.equals(UConst.ZERO))) isModified = true;
        if (expr.subTerms().isEmpty()) {
          isModified = true;
          expr = UConst.zero();
        }
      }
      case MULTIPLY -> {
        if (expr.subTerms().removeIf(subTerm -> subTerm.equals(UConst.ONE))) isModified = true;
        if (expr.subTerms().isEmpty()) {
          isModified = true;
          expr = UConst.one();
        }
        if (any(expr.subTerms(), t -> t.equals(UConst.ZERO))) {
          isModified = true;
          expr = UConst.zero();
        }
      }
      case PRED -> {
        UPred pred = (UPred) expr;
        if(pred.isPredKind(UPred.PredKind.EQ)) {
          assert expr.subTerms().size() == 2;
          List<UTerm> subTerms = expr.subTerms();
          if(subTerms.get(0).kind() == CONST && subTerms.get(1).kind() ==CONST) {
            UConst firstConst = (UConst) subTerms.get(0);
            UConst secondConst = (UConst) subTerms.get(1);
            if(firstConst.value() == secondConst.value())
              expr = UConst.one();
            else
              expr = UConst.zero();
          }
        }
      }
      case SQUASH, NEGATION -> {
        final UTerm body = ((UUnary) expr).body();
        if (body.kind() == CONST && ((UConst) body).isZeroOneVal()) {
          isModified = true;
          if (expr.kind() == SQUASH) expr = body;
          else expr = body.equals(UConst.ONE) ? UConst.zero() : UConst.one();
        }
      }
      case SUMMATION -> {
        final UTerm body = ((USum) expr).body();
        assert body.kind().isBinary();
        if (body.subTerms().size() == 1 && body.subTerms().get(0).equals(UConst.ZERO)) {
          isModified = true;
          expr = UConst.zero();
        }
      }
      default -> {}
    }
    return expr;
  }

  /** fold the constants, such as 1+2 -> 3 * */
  UTerm constantFolding(UTerm expr) {
    expr = transformSubTerms(expr, this::constantFolding);
    switch (expr.kind()) {
      case ADD -> {
        List<UTerm> subTerms = expr.subTerms();
        List<UTerm> newSubTerms = new ArrayList<>();
        int count = 0;
        int foldingVal = 0;
        for(UTerm subTerm : subTerms) {
          if(subTerm.equals(UConst.nullVal())) return expr;
          if(subTerm.kind() == CONST) {
            foldingVal += ((UConst) subTerm).value();
            count++;
          }
          else
            newSubTerms.add(subTerm);
        }
        if(count <= 1) return expr;
        isModified = true;
        newSubTerms.add(UConst.mk(foldingVal));
        return UAdd.mk(newSubTerms);
      }
      case MULTIPLY -> {
        List<UTerm> subTerms = expr.subTerms();
        List<UTerm> newSubTerms = new ArrayList<>();
        int count = 0;
        int foldingVal = 1;
        for(UTerm subTerm : subTerms) {
          if(subTerm.equals(UConst.nullVal())) return expr;
          if(subTerm.kind() == CONST){
            foldingVal *= ((UConst) subTerm).value();
            count++;
          }
          else
            newSubTerms.add(subTerm);
        }
        if(count <= 1) return expr;
        isModified = true;
        newSubTerms.add(UConst.mk(foldingVal));
        return UMul.mk(newSubTerms);
      }
      default -> {}
    }

    return expr;
  }

  /**
   remove squash if its body is add, and its subterms must be STRING EQ pred
   ||[VAR = STRING] + [VAR = STRING]|| -> [VAR = STRING] + [VAR = STRING]
   * */
  UTerm removeSquashClassify(UTerm expr) {
    expr = transformSubTerms(expr, this::removeSquashClassify);

    final UKind kind = expr.kind();
    if (kind != SQUASH) return expr;

    USquash squash = (USquash) expr;
    if(squash.body().kind() != ADD) return expr;

    UAdd add = (UAdd) squash.body();
    for(final UTerm subTerm : add.subTerms()) {
      if(subTerm instanceof UPred pred) {
        if(!pred.isPredKind(UPred.PredKind.EQ)) return expr;
        assert pred.args().size() == 2;
        UTerm firstArg = pred.args().get(0);
        UTerm secondArg = pred.args().get(1);
        if(!(firstArg.kind() == VAR && secondArg.kind() == STRING
                || firstArg.kind() == STRING && secondArg.kind() == VAR)) return expr;
      } else return expr;
    }

    isModified = true;

    return add;
  }

  UTerm expandSquashString(UTerm expr) {
    expr = transformSubTerms(expr, this::expandSquashString);

    final UKind kind = expr.kind();
    if (kind != SUMMATION) return expr;

    final USum summation = (USum) expr;
    final Set<UVar> boundedVars = summation.boundedVars();
    final List<UTerm> subTerms = summation.body().subTerms();
    final List<UTerm> squashedTerms = new ArrayList<>();
    final List<UTerm> toCombine = new ArrayList<>();
    boolean flag = false;
    for(final UTerm subTerm : subTerms) {
      if(subTerm.kind() == SQUASH) {
        final USquash squash = (USquash) subTerm;
        final List<UTerm> squashSubTerms = squash.subTerms();
        if(squashSubTerms.size() == 1 && squashSubTerms.get(0).kind() == ADD) { // squash only has one child of add
          final UAdd add = (UAdd) squashSubTerms.get(0);
          if(add.subTerms().size() >= 3) {
            for(final UTerm addTerm : add.subTerms()) { // check the add subTerms situation
              if(addTerm.kind() == PRED) {
                final UPred pred = (UPred) addTerm;
                if(pred.isPredKind(UPred.PredKind.EQ)) {
                  assert pred.args().size() == 2;
                  final UTerm arg0 = pred.args().get(0), arg1 = pred.args().get(1);
                  if (((arg0.kind() == VAR && arg1.kind() == STRING) ||
                    (arg1.kind() == VAR && arg0.kind() == STRING))) {
                    squashedTerms.add(addTerm);
                    flag = true;
                  }
                } else return expr;
              } else return expr;
            }
          }
        }
      } else toCombine.add(subTerm);
    }
    if(!flag) return expr;

    this.isModified = true;
    final List<UTerm> mulList = new ArrayList<>();
    for(final UTerm squashedTerm : squashedTerms) {
      final USquash squash = USquash.mk(squashedTerm);
      final UMul mulBody = UMul.mk(squash, toCombine);
      mulList.add(mulBody);
    }
    final UAdd addBody = UAdd.mk(mulList);
//    System.out.println("====1" + expr);
    final USum result = USum.mk(boundedVars, addBody);
//    System.out.println("====2" + result);

    return result;

  }

  /**
   apply function to reduce redundant function
   upper('exam') -> 'EXAM'
   * */
  UTerm applyReduceFunc(UTerm expr) {
    expr = transformSubTerms(expr, this::applyReduceFunc);

    final UKind kind = expr.kind();
    if (kind != FUNC) return expr;

    final UFunc func = (UFunc) expr;
    final UName funcName = func.funcName();
    final List<UTerm> arguments = func.args();
    if(arguments.size() == 0) return expr;
    if(arguments.get(0).kind() != FUNC) return expr;

    switch (funcName.toString()) {
      case "`upper`", "`lower`" -> {
        assert arguments.size() == 1;
        final UFunc subFunc = (UFunc) arguments.get(0);
        if(Objects.equals(subFunc.funcName().toString(), "`upper`")
                || Objects.equals(subFunc.funcName().toString(), "`lower`"))
          return UFunc.mk(UFunc.FuncKind.STRING, funcName, subFunc.args());
      }
      default -> {
        return expr;
      }
    }
    return expr;
  }

  /**
   apply function to transform into result of function
   upper('exam') -> 'EXAM'
   * */
  UTerm applyFuncString(UTerm expr) {
    expr = transformSubTerms(expr, this::applyFuncString);

    final UKind kind = expr.kind();
    if (kind != FUNC) return expr;

    final UFunc func = (UFunc) expr;
    final UName funcName = func.funcName();
    final List<UTerm> arguments = func.args();
    if(arguments.size() == 0) return expr;
    if(any(arguments, t -> t.kind() != STRING && t.kind() != CONST)) return expr;

    switch (funcName.toString()) {
      case "`substring`" -> {
        final UString str = (UString) arguments.get(0);
        if(arguments.size() == 3) {
          final Integer start = ((UConst)arguments.get(1)).value();
          final Integer length = ((UConst)arguments.get(2)).value();
          String value = str.value();
          value = value.substring(start - 1, start + length - 1);
          return UString.mk(value);
        } else if(arguments.size() == 2) {
          final Integer start = ((UConst)arguments.get(1)).value();
          String value = str.value();
          value = value.substring(start - 1);
          return UString.mk(value);
        }
        assert false; // should not reach here
      }
      case "`upper`" -> {
        assert arguments.size() == 1;
        final UString str = (UString) arguments.get(0);
        final String value = str.value();
        return UString.mk(value.toUpperCase());
      }
      case "`lower`" -> {
        assert arguments.size() == 1;
        final UString str = (UString) arguments.get(0);
        final String value = str.value();
        return UString.mk(value.toLowerCase());
      }
      case "`concat`" -> {
        assert arguments.size() == 2;
        final UString str1 = (UString) arguments.get(0);
        final UString str2 = (UString) arguments.get(1);
        final String value1 = str1.value();
        final String value2 = str2.value();
        return UString.mk(value1.concat(value2));
      }
      default -> throw new IllegalArgumentException("unknown function name: " + funcName.toString());
    }

    return expr;
  }

  /**
   if one var EQ str1 and EQ str2, and str1 != str2, return 0
   [a = 'str1'] * [a = 'str2'] -> 0
   * */
  UTerm removeRedundantString(UTerm expr) {
    expr = transformSubTerms(expr, this::removeRedundantString);

    final UKind kind = expr.kind();
    if (kind != MULTIPLY) return expr;

    final UMul mul = (UMul) expr;
    NaturalCongruence<UTerm> congruence = UExprSupport.getEqVarStringCongruenceInTermsOfMul(mul);
    for (UTerm key : congruence.keys()) {
      // for each congruence class
      Set<UTerm> eqClass = congruence.eqClassAt(key);
      UString uString = null;
      for (UTerm term : eqClass) {
        if (term instanceof UString s) {
          if (uString == null) uString = s;
          // two different strings never equal
          else if (!uString.equals(s)) return UConst.zero();
        }
      }
    }
    return expr;
  }

  /**
   if multiply terms has NULL return 0
   E1 * NULL * E2 * ... -> 0
   * */
  UTerm removeNullMultiplication(UTerm expr) {
    expr = transformSubTerms(expr, this::removeNullMultiplication);

    final UKind kind = expr.kind();
    if (kind != MULTIPLY) return expr;

    final List<UTerm> subTerms = expr.subTerms();
    if(subTerms.size() > 1) {
      boolean hasNull = false;
      boolean hasNotNullTerm = false;
      for(final UTerm subTerm : subTerms) {
        if(subTerm.equals(UConst.nullVal()))
          hasNull = true;
        else hasNotNullTerm = true;
      }
      if(hasNull && hasNotNullTerm) {
        isModified = true;
        expr = UConst.zero();
      }
    }
    return expr;
  }
}

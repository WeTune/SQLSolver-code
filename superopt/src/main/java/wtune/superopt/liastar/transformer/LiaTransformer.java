package wtune.superopt.liastar.transformer;

import wtune.common.utils.SetSupport;
import wtune.superopt.liastar.LiaAndImpl;
import wtune.superopt.liastar.LiaStar;
import wtune.superopt.liastar.LiaVarImpl;
import wtune.superopt.logic.Z3Support;

import java.util.*;

import static wtune.superopt.liastar.transformer.VectorSupport.*;

/**
 * Transform plain LIA* formula (without nested stars, parameters and non-linear terms) into an
 * equivalent LIA formula. The LIA* formula should be in this form: g /\ v,_ in {w|f}*. In case of
 * exceptions, the resulting LIA formula is an over-approximation of the original LIA* formula.
 */
public class LiaTransformer {
  /**
   * Transform plain LIA* formula (without nested stars, parameters and non-linear terms)
   * into an equivalent LIA formula.
   * The LIA* formula should be given in this form:
   * (v, _) in {w | f /\ s}*,
   * where (v, _) and w have the same number of dimensions,
   * f does not contain formulas from expanding stars,
   * and s contains formulas from expanding stars.
   * An external constraint g may accelerate the transformation:
   * if the LIA* formula contradicts g, then this method returns a LIA formula representing "false".
   * Inaccurate partition between f and s may affect proof ability.
   * If transformation into an equivalent LIA formula fails, return an over-approximation.
   *
   * @param g the external constraint
   * @param f the part of constraint that has no formula from expanding stars;
   *          <code>null</code> indicates absence of this part
   * @param s the part of constraint that contains formulas from expanding stars;
   *          <code>null</code> indicates absence of this part
   * @return equivalent or over-approximation of "(v, _) in {w | f /\ s}*" under the constraint g
   *         (i.e. a LIA formula L such that "g /\ L" iff (or if) "g /\ (v, _) in {w | f /\ s}*")
   */
  public LiaStar transform(LiaStar g, List<String> v, List<String> w, LiaStar f, LiaStar s) {
    if (f == null) {
      f = LiaStar.mkTrue(true);
    }
    // transform into equivalent LIA
    LiaStar constraint = LiaStar.mkAnd(true, f, s);
    // fast routine: detect contradiction
    if (contradicts(g, v, w, constraint)) {
      return LiaStar.mkFalse(g.isInStar());
    }
    // regular routine: compute equivalent LIA
    try {
      return transformEquivalent(g, v, w, constraint);
    } catch (RuntimeException ignored) {}
    // if fails, transform into over-approximation
    return transformOverApprox(g, v, w, f, s);
  }

  // whether "g /\ (v, _) in {w | f}*" is UNSAT
  private boolean contradicts(LiaStar g, List<String> v, List<String> w, LiaStar f) {
    // "g(v) /\ (v, _) in {(w1, w2) | f(w1, w2)}*" is UNSAT
    // if all of these are true:
    // (1) g(0) is UNSAT
    // (2) forall w1. (exists w2. f(w1, w2)) -> g(w1) is UNSAT
    // (3) forall x, y. g(x) is UNSAT /\ g(y) is UNSAT -> g(x + y) is UNSAT

    // Condition 1: "not g(0)" is valid (i.e. always true)
    final LiaStar cond1 = LiaStar.mkNot(false, apply(g, v, constToLia(constZero(v.size()))));
    if (!Z3Support.isValidLia(cond1, cond1.collectVarSet())) {
      return false;
    }

    // Condition 2: forall w1,w2,x. f(w1, w2) -> not g(w1)
    // x are the variables in g besides w1
    final int vSize = v.size();
    final List<String> w1 = w.subList(0, vSize);
    final LiaStar cond2Csq = LiaStar.mkNot(false, apply(g, v, nameToLia(w1)));
    final LiaStar cond2 = LiaStar.mkImplies(false, f, cond2Csq);
    if (!Z3Support.isValidLia(cond2, cond2.collectVarSet())) {
      return false;
    }

    // Condition 3: forall x,y,z3. exists z1,z2.
    //   g(x) \/ g(y) \/ not g(x + y)
    // z1,z2,z3 are vars in the 1st/2nd/3rd occurrence of g besides args (x/y/x+y)
    // TODO: (assumption) g does not contain var names like "contra_..."
    final List<String> x = createVarVector("contra_x", 0, vSize);
    final List<String> y = createVarVector("contra_y", 0, vSize);
    // rename vars in g to z1,z2,z3
    Set<String> usedVarNames = g.collectVarSet();
    final LiaStar g1 = g.deepcopy().transformPostOrder(fm -> renameVarsBesides(fm, v, usedVarNames));
    final LiaStar g2 = g.deepcopy().transformPostOrder(fm -> renameVarsBesides(fm, v, usedVarNames));
    final LiaStar g3 = g.deepcopy().transformPostOrder(fm -> renameVarsBesides(fm, v, usedVarNames));
    // construct condition 3
    final List<LiaStar> cond3Parts = new ArrayList<>();
    cond3Parts.add(apply(g1, v, nameToLia(x)));
    cond3Parts.add(apply(g2, v, nameToLia(y)));
    cond3Parts.add(LiaStar.mkNot(false, apply(g3, v, plus(nameToLia(x), nameToLia(y)))));
    final LiaStar cond3 = LiaStar.mkDisjunction(false, cond3Parts);
    return Z3Support.isValidLia(cond3, cond3Parts.get(2).collectVarSet());
  }

  // rename vars in f except those in "besides"
  // "used" records used var names so vars are not renamed to them
  private LiaStar renameVarsBesides(LiaStar f, Collection<String> besides, Collection<String> used) {
    if (f instanceof LiaVarImpl var) {
      final String oldName = var.getName();
      if (besides.contains(oldName)) {
        return f;
      }
      // find an unused name
      int count = 1;
      String newName;
      do {
        newName = oldName + "_" + count++;
      } while (used.contains(newName));
      // rename
      used.add(newName);
      return LiaStar.mkVar(f.isInStar(), newName);
    }
    return f;
  }

  private LiaStar transformEquivalent(LiaStar g, List<String> v, List<String> w, LiaStar f) {
    return transformSls(g, v, w, f);
  }

  private LiaStar transformOverApprox(LiaStar g, List<String> v, List<String> w, LiaStar f, LiaStar s) {
    //System.out.println("fallback");
    // make implication from f /\ s
    LiaStar constraint = LiaStar.mkAnd(true, f, s);
    LiaStar overApprox = transformFallback(v, w, constraint);
    // transform part of f /\ s into SLS then LIA
    if (s != null) {
      // transform f into SLS then LIA
      //System.out.println("small sls");
      try {
        overApprox = LiaStar.mkAnd(true, overApprox, transformSls(g, v, w, f));
      } catch (RuntimeException ignored) {
        // if fails, transform only part of f related to v into SLS then LIA
        //System.out.println("smaller sls");
        try {
          overApprox = LiaStar.mkAnd(true, overApprox, transformSls(g, v, w, removeUnrelatedTerms(f, w.subList(0, v.size()))));
        } catch (RuntimeException ignored1) {}
      }
    } else {
      // when s is absent, transforming f is redundant
      // transform only part of f related to v
      //System.out.println("smaller sls");
      try {
        overApprox = LiaStar.mkAnd(true, overApprox, transformSls(g, v, w, removeUnrelatedTerms(f, w.subList(0, v.size()))));
      } catch (RuntimeException ignored) {}
    }
    return overApprox;
  }

  private LiaStar removeUnrelatedTerms(LiaStar f, List<String> vars) {
    // destruct f into terms connected by AND
    List<LiaStar> terms = new ArrayList<>();
    if (f instanceof LiaAndImpl and) {
      and.flatten(terms);
    } else {
      terms.add(f);
    }
    // only collect related terms
    Set<String> varSet = new HashSet<>(vars);
    LiaStar result = LiaStar.mkTrue(f.isInStar());
    for (LiaStar term : terms) {
      if (!SetSupport.intersect(term.collectVarSet(), varSet).isEmpty()) {
        result = LiaStar.mkAnd(f.isInStar(), result, term);
      }
    }
    //System.out.println("removeUnrelatedTerms: " + result);
    return result;
  }

  // compute SLS for "(v, _) in {w | f}*" under constraint g
  private LiaStar transformSls(LiaStar g, List<String> v, List<String> w, LiaStar f) {
    // SLS of the under-approximation
    List<String> slsVector = w.subList(0, v.size());
    final SlsAugmenter underApprox = new SlsAugmenter(slsVector, f);
    // Maintain under-approx u and (optional) over-approx o
    // Repeat:
    // 1. weaken u
    // 2. (optional; do not do this when u has been SAT) strengthen o
    // until g/\o becomes UNSAT (return 1 = 0)
    // or u becomes over-approximation (return u)
    int count = 0;
    while (true) {
      //System.out.println("augment " + ++count);
      // try to weaken u
      boolean b = underApprox.augment();
      //System.out.println("sls = " + underApprox.sls());
      if (!b) {
        // no augmentation is found
        // u has become over-approximation
        LiaStar underLia = underApprox.sls().toStarLia(slsVector);
        return apply(underLia, slsVector, nameToLia(v));
      }
      // TODO: (optional) strengthen over-approximation o
      //  if g/\o is UNSAT, return "1 = 0"
    }
  }

  // Invoked if SLS is unknown.
  // Given "(v,_) in {w|f}*",
  // it tries to provide its over-approximation via heuristics.
  private LiaStar transformFallback(List<String> v, List<String> w, LiaStar f) {
    // generate over-approximation of "(v,_) in {w|f}*"
    // i.e. make implications from that LIA* formula
    LiaStar conclusionVarEq = implyVarEq(v, w, f);
    LiaStar conclusionNonZeroImplication = implyZeroImplication(v, w, f);
    return LiaStar.mkAnd(false, conclusionVarEq, conclusionNonZeroImplication);
  }

  // make implications like "v1 = v2" from f
  private LiaStar implyVarEq(List<String> v, List<String> w, LiaStar f) {
    LiaStar result = LiaStar.mkTrue(false);
    for (int i = 0; i < v.size(); i++) {
      String outVar1 = v.get(i);
      String inVar1 = w.get(i);
      for (int j = i + 1; j < v.size(); j++) {
        String outVar2 = v.get(j);
        String inVar2 = w.get(j);
        // equivalence among dimensions of w implies
        // equivalence among dimensions of v
        try {
          if (impliesVarEq(f, inVar1, inVar2)){
            LiaStar outEq = LiaStar.mkEq(false, LiaStar.mkVar(false, outVar1), LiaStar.mkVar(false, outVar2));
            result = LiaStar.mkAnd(false, result, outEq);
          }
        } catch (RuntimeException ignored) {}
      }
    }
    return result;
  }

  // whether f implies v1 = v2
  private boolean impliesVarEq(LiaStar f, String v1, String v2) {
    LiaStar v1EqV2 = LiaStar.mkEq(false, LiaStar.mkVar(false, v1), LiaStar.mkVar(false, v2));
    LiaStar toCheck = LiaStar.mkImplies(false, f, v1EqV2);
    return Z3Support.isValidLia(toCheck, toCheck.collectVarSet());
  }

  // make implications like "v1 = 0 -> v2 = 0" from f
  private LiaStar implyZeroImplication(List<String> v, List<String> w, LiaStar f) {
    LiaStar result = LiaStar.mkTrue(false);
    for (int i = 0; i < v.size(); i++) {
      String outVar1 = v.get(i);
      String inVar1 = w.get(i);
      for (int j = 0; j < v.size(); j++) {
        if (i == j) {
          continue;
        }
        String outVar2 = v.get(j);
        String inVar2 = w.get(j);
        // for each pair of dimensions w1 and w2 in w
        // if w1 = 0 -> w2 = 0
        // then for its corresponding dimensions v1 and v2 in v
        // we have v1 = 0 -> v2 = 0
        try {
          if (impliesZeroImplication(f, inVar1, inVar2)){
            LiaStar nonZeroW1 = LiaStar.mkEq(false, LiaStar.mkVar(false, outVar1), LiaStar.mkConst(false, 0));
            LiaStar nonZeroW2 = LiaStar.mkEq(false, LiaStar.mkVar(false, outVar2), LiaStar.mkConst(false, 0));
            LiaStar nonZeroImplication = LiaStar.mkImplies(false, nonZeroW1, nonZeroW2);
            result = LiaStar.mkAnd(false, result, nonZeroImplication);
          }
        } catch (RuntimeException ignored) {}
      }
    }
    return result;
  }

  // whether f implies "v1 = 0 -> v2 = 0"
  private boolean impliesZeroImplication(LiaStar f, String v1, String v2) {
    LiaStar nonZeroV1 = LiaStar.mkEq(false, LiaStar.mkVar(false, v1), LiaStar.mkConst(false, 0));
    LiaStar nonZeroV2 = LiaStar.mkEq(false, LiaStar.mkVar(false, v2), LiaStar.mkConst(false, 0));
    LiaStar nonZeroImplication = LiaStar.mkImplies(false, nonZeroV1, nonZeroV2);
    LiaStar toCheck = LiaStar.mkImplies(false, f, nonZeroImplication);
    return Z3Support.isValidLia(toCheck, toCheck.collectVarSet());
  }
}

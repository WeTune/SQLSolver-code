package wtune.superopt.liastar;

import wtune.common.utils.SetSupport;
import wtune.superopt.logic.Z3Support;

import java.util.*;
import java.util.function.BiFunction;

public class LiaStarSimplifier {
  /**
   * Map from LIA* to T.
   * Equality among LIA* formulas is determined using SMT solver
   * instead of the "equals" method.
   */
  private static class LiaStarMap<T> {
    private final List<LiaStar> keys;
    private final List<T> values;
    BiFunction<LiaStar, LiaStar, Boolean> comparator;

    LiaStarMap(BiFunction<LiaStar, LiaStar, Boolean> comparator) {
      keys = new ArrayList<>();
      values = new ArrayList<>();
      this.comparator = comparator;
    }

    int getIndex(LiaStar lia) {
      int count = 0;
      for (LiaStar key : keys) {
        if (comparator.apply(lia, key)) {
          return count;
        }
        count++;
      }
      return -1;
    }

    T get(LiaStar lia) {
      final int index = getIndex(lia);
      if (index >= 0) {
        return values.get(index);
      }
      return null;
    }

    void put(LiaStar lia, T value) {
      final int index = getIndex(lia);
      if (index >= 0) {
        values.set(index, value);
      } else {
        keys.add(lia);
        values.add(value);
      }
    }
  }

  private static final LiaStarSimplifier simplifier = new LiaStarSimplifier();

  public static LiaStarSimplifier getInstance() {
    return simplifier;
  }

  private LiaStarSimplifier() {}

  public LiaStar simplify(LiaStar f) {
    f = f.simplifyIte();
    f = f.transformPostOrder(this::collapseConsecutiveStars);
    f = f.transformPostOrder(this::removeRedundantInnerVars);
    //f = f.transformPostOrder(this::unifyExprOccurrences);
    //f = f.transformPostOrder(this::mergeIteConditions);
    return f;
  }

  /*
   * +================================+
   * | Rule: collapseConsecutiveStars |
   * +================================+
   */

  /**
   * v0,_ ∈ {(v1, v2) | v1 = v2 /\ v2 ∈ {(v3, v4) | ...}*}*
   * ->
   * v0,_ ∈ {(v3, v4) | ...}*
   * <br/>
   * where v0,_,v1,v2,v3,v4 are vectors of the same length
   */
  private LiaStar collapseConsecutiveStars(LiaStar f) {
    if (f instanceof LiaSumImpl star) {
      // determine v0,v1
      ArrayList<String> v0 = star.outerVector;
      int length = v0.size();
      List<String> v1 = star.innerVector.subList(0, length);

      // determine v2 & check the form of formula
      LiaSumImpl innerStar = extractInnerStar(star.constraints, v1);
      if (innerStar == null) return f;

      // eliminate the outer star
      return LiaStar.mkSum(star.innerStar, v0,
              innerStar.innerVector, innerStar.constraints);
    }
    return f;
  }

  /**
   * Return the inner star if constraints is in the form
   * "v1 = v2 /\ v2 ∈ {(v3, v4) | ...}*"
   * or null otherwise
   * The order of dimensions of a vector can be adjusted if necessary.
   */
  private LiaSumImpl extractInnerStar(LiaStar constraints, List<String> v1) {
    if (constraints instanceof LiaAndImpl and) {
      // flatten the "AND"
      List<LiaStar> props = new LinkedList<>();
      and.flatten(props);

      // traverse & check validity
      // determine v2 and v3
      LiaSumImpl star = null;
      Map<String, String> v1ToV2 = new HashMap<>();
      for (LiaStar prop : props) {
        if (prop instanceof LiaEqImpl eq) {
          // handle the equation
          if (!matchV1V2(v1, eq, v1ToV2)) return null;
        } else if (prop instanceof LiaSumImpl star0) {
          // star is processed at the end
          if (star == null) star = star0;
          else return null; // multiple stars
        } else {
          // unexpected constraint
          return null;
        }
      }

      // check whether the map and v1 are consistent
      // also extract the expected v2
      ArrayList<String> expectedV2 = new ArrayList<>();
      for (String dimV1 : v1) {
        // for each dimension in v1 (i.e. dimV1)
        String dimV2 = v1ToV2.get(dimV1);
        if (dimV2 == null) return null; // missing equation for dimV1
        expectedV2.add(dimV2);
      }

      // process the star: rearrange v2,v3
      if (star == null) return null; // missing a star
      List<String> actualV2 = star.outerVector;
      List<String> oldV3V4 = star.innerVector;
      ArrayList<String> newV3V4 = reorder(actualV2, expectedV2, oldV3V4);
      return (LiaSumImpl) LiaStar.mkSum(
              star.innerStar, expectedV2, newV3V4, star.constraints);
    }
    return null;
  }

  private boolean matchV1V2(String dimV1, String dimV2, Map<String, String> v1ToV2) {
    String old = v1ToV2.put(dimV1, dimV2);
    return old == null || old.equals(dimV2);
  }

  private boolean matchV1V2(List<String> v1, LiaEqImpl eq, Map<String, String> v1ToV2) {
    if (eq.operand1 instanceof LiaVarImpl left
            && eq.operand2 instanceof LiaVarImpl right) {
      if (v1.contains(left.varName) && !v1.contains(right.varName)) {
        // v1[x] = v2[x]
        return matchV1V2(left.varName, right.varName, v1ToV2);
      } else if (!v1.contains(left.varName) && v1.contains(right.varName)) {
        // v2[x] = v1[x]
        return matchV1V2(right.varName, left.varName, v1ToV2);
      }
    }
    return false;
  }

  /**
   * Reorder "source" using the same permutation
   * from "refSource" to "refTarget".
   * <br/>
   * For example, refSource=(1,2,3) and refTarget=(3,2,1)
   * indicate a reverse of a 3-element list,
   * so the first 3 elements in "source", say (10,7,4),
   * are reversed and become (4,7,10).
   */
  private <T, U> ArrayList<U> reorder(List<T> refSource, List<T> refTarget,
                                      List<U> source) {
    // compute the permutation
    List<Integer> indexMap = new ArrayList<>();
    int refSize = refSource.size();
    assert refSize == refTarget.size();
    for (T elementSrc : refSource) {
      int toIndex = refTarget.indexOf(elementSrc);
      indexMap.add(toIndex);
    }

    // apply the permutation
    ArrayList<U> target = new ArrayList<>(source);
    for (int i = 0; i < refSize; i++) {
      int toIndex = indexMap.get(i);
      target.set(toIndex, source.get(i));
    }
    return target;
  }

  /*
   * +================================+
   * | Rule: removeRedundantInnerVars |
   * +================================+
   */

  /**
   * u = v /\ (..., v, ...) in {...}* /\ P
   * (the star set and P do not use v)
   * ->
   * (..., u, ...) in {...}* /\ ...
   */
  public LiaStar removeRedundantInnerVars(LiaStar f, LiaStar parent) {
    if (!(parent instanceof final LiaSumImpl sum)) {
      return f;
    }
    // flatten AND
    List<LiaStar> conds = new ArrayList<>();
    if (f instanceof LiaAndImpl and) {
      and.flatten(conds);
    } else {
      conds.add(f);
    }
    // check whether each (unimportant) inner var is redundant
    List<String> redundantVars = new ArrayList<>();
    for (String var : sum.innerVector.subList(sum.outerVector.size(), sum.innerVector.size())) {
      conds = removeRedundantInnerVar(var, conds, redundantVars);
    }
    // also remove redundant inner vars from the inner vector
    sum.innerVector.removeAll(redundantVars);
    return LiaStar.mkConjunction(f.innerStar, conds);
  }

  // Check whether every formula in conds is one of these cases:
  // - "u = var" or "var = u", where u is not var
  // (only one u should be present, i.e. no "u1=var /\ u2=var" where u1,u2 are different)
  // - "(...var...) in {...}*"
  // (this should appear exactly once)
  // - a formula that does not contain var
  // If so, merge the first two types of formulas in conds
  // (i.e. remove var and use "u" instead),
  // and add var to redundantVars.
  private List<LiaStar> removeRedundantInnerVar(String var, List<LiaStar> conds, List<String> redundantVars) {
    final List<LiaStar> newConds = new ArrayList<>();
    LiaSumImpl targetStar = null;
    String targetU = null;
    for (LiaStar cond : conds) {
      final String u = uOfUEqVar(cond, var);
      if (u != null) {
        // Case 1
        if (targetU == null) {
          targetU = u;
          continue;
        } else if (targetU.equals(u)) {
          // duplicated cond; skip
          continue;
        } else {
          // vars are not redundant
          return conds;
        }
      } else if (cond instanceof LiaSumImpl star && star.outerVector.contains(var)) {
        // Case 2 (should only appear once)
        if (targetStar == null) {
          targetStar = (LiaSumImpl) star.deepcopy();
          continue;
        } else {
          // "vars in {...}*" should appear at most once
          return conds;
        }
      }
      // Case 3. cond should not contain var
      if (!cond.collectAllVars().contains(var)) {
        newConds.add(cond);
        continue;
      }
      // vars are not redundant
      return conds;
    }
    // "u = var" or "var = u" should appear
    // "(...var...) in {...}*" should appear
    if (targetU == null || targetStar == null) {
      return conds;
    }
    // vars are redundant
    // remove redundant vars (i.e. merge case 1 & 2 into one star)
    final String u = targetU;
    targetStar.outerVector.replaceAll(v -> v.equals(var) ? u : v);
    newConds.add(targetStar);
    redundantVars.add(var);
    return newConds;
  }

  // whether f is "u = var" or "var = u" where u is not var
  // return u
  private String uOfUEqVar(LiaStar f, String var) {
    if (f instanceof LiaEqImpl eq) {
      final LiaStar left = eq.operand1;
      final LiaStar right = eq.operand2;
      if (left instanceof LiaVarImpl lv && right instanceof LiaVarImpl rv) {
        if (var.equals(lv.varName) && !var.equals(rv.varName)) {
          return rv.varName;
        } else if (!var.equals(lv.varName) && var.equals(rv.varName)) {
          return lv.varName;
        }
      }
    }
    return null;
  }
}

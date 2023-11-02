package wtune.superopt.liastar;

import java.util.*;

public class LiaStarSimplifier {

  private static final LiaStarSimplifier simplifier = new LiaStarSimplifier();

  public static LiaStarSimplifier getInstance() {
    return simplifier;
  }

  private LiaStarSimplifier() {}

  private boolean matchV1V2(String dimV1, String dimV2, Map<String, String> v1ToV2) {
    String old = v1ToV2.put(dimV1, dimV2);
    return old == null || old.equals(dimV2);
  }

  private boolean matchV1V2(List<String> v1, LiaeqImpl eq, Map<String, String> v1ToV2) {
    if (eq.operand1 instanceof LiavarImpl left
            && eq.operand2 instanceof LiavarImpl right) {
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

  /**
   * Return the inner star if constraints is in the form
   * "v1 = v2 /\ v2 ∈ {(v3, v4) | ...}*"
   * or null otherwise
   * The order of dimensions of a vector can be adjusted if necessary.
   */
  private LiasumImpl extractInnerStar(Liastar constraints, List<String> v1) {
    if (constraints instanceof LiaandImpl and) {
      // flatten the "AND"
      List<Liastar> props = new LinkedList<>();
      and.flatten(props);

      // traverse & check validity
      // determine v2 and v3
      LiasumImpl star = null;
      Map<String, String> v1ToV2 = new HashMap<>();
      for (Liastar prop : props) {
        if (prop instanceof LiaeqImpl eq) {
          // handle the equation
          if (!matchV1V2(v1, eq, v1ToV2)) return null;
        } else if (prop instanceof LiasumImpl star0) {
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
      ArrayList<String> actualV2 = star.outerVector;
      ArrayList<String> oldV3V4 = star.innerVector;
      ArrayList<String> newV3V4 = reorder(actualV2, expectedV2, oldV3V4);
      return (LiasumImpl) Liastar.mkSum(
              star.innerStar, expectedV2, newV3V4, star.constraints);
    }
    return null;
  }

  /**
   * v0 ∈ {(v1, v2) | v1 = v2 /\ v2 ∈ {(v3, v4) | ...}*}*
   * ->
   * v0 ∈ {(v3, v4) | ...}*
   * <br/>
   * where v0,v1,v2,v3,v4 are vectors of the same length
   */
  private Liastar collapseConsecutiveStars(Liastar f) {
    if (f instanceof LiasumImpl star) {
      // determine v0,v1
      ArrayList<String> v0 = star.outerVector;
      int length = v0.size();
      List<String> v1 = star.innerVector.subList(0, length);

      // determine v2 & check the form of formula
      LiasumImpl innerStar = extractInnerStar(star.constraints, v1);
      if (innerStar == null) return f;

      // eliminate the outer star
      return Liastar.mkSum(star.innerStar, v0,
              innerStar.innerVector, innerStar.constraints);
    }
    return f;
  }

  public Liastar simplify(Liastar f) {
    f = f.simplifyIte();
    f = f.transformPostOrder(this::collapseConsecutiveStars);
    return f;
  }

}

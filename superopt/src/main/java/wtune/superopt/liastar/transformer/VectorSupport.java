package wtune.superopt.liastar.transformer;

import wtune.superopt.liastar.LiaStar;
import wtune.superopt.liastar.LiaVarImpl;

import java.util.ArrayList;
import java.util.List;
import java.util.function.BiFunction;

public class VectorSupport {
  /** Return a + b. */
  public static List<LiaStar> plus(List<LiaStar> a, List<LiaStar> b) {
    assert a.size() == b.size();
    List<LiaStar> vector = new ArrayList<>();
    for (int i = 0, bound = a.size(); i < bound; i++) {
      vector.add(LiaStar.mkPlus(false, a.get(i), b.get(i)));
    }
    return vector;
  }

  /** Return coefficient * a. */
  public static List<LiaStar> times(List<LiaStar> a, LiaStar coefficient) {
    return a.stream().map(x -> LiaStar.mkMult(false, x, coefficient)).toList();
  }

  /** Return rel(a, b). */
  public static LiaStar vectorRel(List<LiaStar> a, List<LiaStar> b, BiFunction<LiaStar, LiaStar, LiaStar> rel) {
    final int size = a.size();
    assert size == b.size();
    if (size == 0) {
      return LiaStar.mkTrue(false);
    }
    LiaStar result = rel.apply(a.get(0), b.get(0));
    for (int i = 1; i < size; i++) {
      result = LiaStar.mkAnd(false, result, LiaStar.mkEq(false, a.get(i), b.get(i)));
    }
    return result;
  }

  /** Return a = b. */
  public static LiaStar eq(List<LiaStar> a, List<LiaStar> b) {
    return vectorRel(a, b, (x, y) -> LiaStar.mkEq(false, x, y));
  }

  /** Return a <= b. */
  public static LiaStar le(List<LiaStar> a, List<LiaStar> b) {
    return vectorRel(a, b, (x, y) -> LiaStar.mkLe(false, x, y));
  }

  /** Return a >= 0. */
  public static LiaStar nonNegative(List<LiaStar> a) {
    final int size = a.size();
    if (size == 0) {
      return LiaStar.mkTrue(false);
    }
    LiaStar result = LiaStar.mkLe(false, LiaStar.mkConst(false, 0), a.get(0));
    for (int i = 1; i < size; i++) {
      result = LiaStar.mkAnd(false, result, LiaStar.mkLe(false, LiaStar.mkConst(false, 0), a.get(i)));
    }
    return result;
  }

  /**
   * Apply the formula as a function with arguments (i.e. formula(args)). This method does not
   * change the original formula.
   *
   * @param formula the formula as a function
   * @param argVars the argument variables of that function
   * @param args the real arguments
   * @return the result of application (replace argVars with args in formula)
   */
  public static LiaStar apply(LiaStar formula, List<String> argVars, List<LiaStar> args) {
    assert argVars.size() == args.size();
    return formula.transformPostOrder(f -> {
      if (f instanceof LiaVarImpl var) {
        String varName = var.getName();
        int index = argVars.indexOf(varName);
        if (index >= 0) {
          return args.get(index).deepcopy();
        }
      }
      return f;
    });
  }

  /** Create a variable vector (prefix_fromIndex ... prefix_[toIndex-1]). */
  public static List<String> createVarVector(String prefix, int fromIndex, int toIndex) {
    List<String> vector = new ArrayList<>();
    for (int i = fromIndex; i < toIndex; i++) {
      vector.add(prefix + "_" + i);
    }
    return vector;
  }

  /**
   * Given coefficients c1 ... cN and vectors v1 ... vN, return their linear combination.
   *
   * @param coefficients the coefficients
   * @param vectors the vectors, which consist of constants
   * @param vectorSize the length of each vector
   * @return the linear combination (i.e. c1*v1 + ... + cN*vN)
   */
  public static List<LiaStar> linearCombination(
          List<LiaStar> coefficients, List<List<Long>> vectors, int vectorSize) {
    final int vectorCount = coefficients.size();
    assert vectorCount == vectors.size();
    List<LiaStar> result = null;
    for (int i = 0; i < vectorCount; i++) {
      LiaStar coefficient = coefficients.get(i);
      List<Long> vector = vectors.get(i);
      assert vector.size() == vectorSize;
      List<LiaStar> product = times(constToLia(vector), coefficient);
      result = result == null ? product : plus(result, product);
    }
    return result == null ? liaZero(vectorSize) : result;
  }

  public static List<LiaStar> liaZero(int size) {
    List<LiaStar> result = new ArrayList<>();
    for (int i = 0; i < size; i++) {
      result.add(LiaStar.mkConst(false, 0));
    }
    return result;
  }

  public static List<Long> constZero(int size) {
    List<Long> result = new ArrayList<>();
    for (int i = 0; i < size; i++) {
      result.add(0L);
    }
    return result;
  }

  public static List<Long> constCopy(List<Long> vector) {
    return new ArrayList<>(vector);
  }

  public static List<Long> constMinus(List<Long> a, List<Long> b) {
    assert a.size() == b.size();
    List<Long> vector = new ArrayList<>();
    for (int i = 0, bound = a.size(); i < bound; i++) {
      vector.add(a.get(i) - b.get(i));
    }
    return vector;
  }

  public static List<LiaStar> constToLia(List<Long> vector) {
    return vector.stream().map(val -> LiaStar.mkConst(false, val)).toList();
  }

  public static List<LiaStar> nameToLia(List<String> vector) {
    return vector.stream().map(name -> LiaStar.mkVar(false, name)).toList();
  }

  /**
   * Given two non-negative vectors (each dimension is non-negative), tell whether each dimension of
   * one vector <= that of the other.
   *
   * @param a one vector
   * @param b the other vector
   * @return whether "0<=a<=b"
   */
  public static boolean constLe(List<Long> a, List<Long> b) {
    final int size = a.size();
    if (b.size() != size) {
      return false;
    }
    for (int i = 0; i < size; i++) {
      if (!(a.get(i) >= 0 && a.get(i) <= b.get(i))) {
        return false;
      }
    }
    return true;
  }

  public static boolean isConstZero(List<Long> a) {
    for (Long aLong : a) {
      if (aLong != 0) {
        return false;
      }
    }
    return true;
  }
}

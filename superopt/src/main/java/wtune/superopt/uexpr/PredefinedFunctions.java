package wtune.superopt.uexpr;

import java.util.List;

public class PredefinedFunctions {

  public static final String NAME_DIVIDE = "divide";
  public static final String NAME_SQRT = "sqrt";
  public static final String NAME_MINUS = "minus";
  public static final String NAME_UPPER = "upper";
  public static final String NAME_LOWER = "lower";
  public static final String NAME_DATE = "Date";
  public static final String NAME_YEAR = "year";
  public static final String NAME_YEAR_QUOTED = "`year`";
  public static final String NAME_LIKE = "like_op";
  public static final String NAME_LIKE_QUOTED = "`like_op`";
  public static final String NAME_IN_LIST = "in_list";

  /**
   * A function family is a collection of functions
   * with a common prefix and different arity.
   */
  public interface FunctionFamily {
    /** Whether the family contains a specific function. */
    boolean contains(String funcName, int arity);
  }

  /**
   * A function (family) with a fixed name and arity.
   * In fact such family contains exactly one function.
   */
  public record FixedArityFunctionFamily(String name, int arity) implements FunctionFamily {
    public boolean contains(String funcName, int arity) {
      return name.equals(funcName) && this.arity == arity;
    }
  }

  /**
   * A family of functions with a common prefix and a variable arity
   * which has a minimum value.
   */
  public record VariableArityFunctionFamily(String prefix, int minArity) implements FunctionFamily {
    public boolean contains(String funcName, int arity) {
      int argCount = PredefinedFunctions.parseArgCount(funcName, prefix);
      return argCount == arity && arity >= minArity;
    }
  }

  // TODO: properties of each function (e.g. LIKE returns only 0 or 1)
  public static final FunctionFamily DIVIDE = new FixedArityFunctionFamily(NAME_DIVIDE, 2);
  public static final FunctionFamily SQRT = new FixedArityFunctionFamily(NAME_SQRT, 1);
  public static final FunctionFamily MINUS = new FixedArityFunctionFamily(NAME_MINUS, 2);
  public static final FunctionFamily UPPER = new FixedArityFunctionFamily(NAME_UPPER, 1);
  public static final FunctionFamily LOWER = new FixedArityFunctionFamily(NAME_LOWER, 1);
  public static final FunctionFamily DATE = new FixedArityFunctionFamily(NAME_DATE, 1);
  public static final FunctionFamily YEAR = new FixedArityFunctionFamily(NAME_YEAR, 1);
  public static final FunctionFamily LIKE = new FixedArityFunctionFamily(NAME_LIKE, 2);
  public static final FunctionFamily YEAR_QUOTED = new FixedArityFunctionFamily(NAME_YEAR_QUOTED, 1);
  public static final FunctionFamily LIKE_QUOTED = new FixedArityFunctionFamily(NAME_LIKE_QUOTED, 2);
  public static final FunctionFamily IN_LIST = new VariableArityFunctionFamily(NAME_IN_LIST, 2);

  public static final List<FunctionFamily> ALL_FUNCTION_FAMILIES = List.of(
          DIVIDE, SQRT, MINUS, UPPER, LOWER, DATE, YEAR, LIKE, IN_LIST
  );

  /** Whether a function returns a non-negative integer. */
  public static boolean returnsNonNegativeInt(String funcName, int arity) {
    return YEAR.contains(funcName, arity)
            || YEAR_QUOTED.contains(funcName, arity)
            || LIKE.contains(funcName, arity)
            || LIKE_QUOTED.contains(funcName, arity)
            || IN_LIST.contains(funcName, arity);
  }

  /**
   * Return (familyName + "_" + argCount). "argCount" must be non-negative.
   */
  public static String instantiateFamilyFunc(String familyName, int argCount) {
    if (argCount < 0) throw new IllegalArgumentException("argCount should be non-negative");
    return familyName + "_" + argCount;
  }

  /**
   * Check whether familyFuncName.equals(familyName + "_" + N) for some non-negative integer N.
   * Return N if so, or -1 otherwise.
   */
  public static int parseArgCount(String familyFuncName, String familyName) {
    if (!familyFuncName.startsWith(familyName)) return -1;
    if (familyFuncName.charAt(familyName.length()) == '_') {
      String suffix = familyFuncName.substring(familyName.length() + 1);
      try {
        int argCount = Integer.parseInt(suffix);
        return argCount >= 0 ? argCount : -1;
      } catch (NumberFormatException e) {
        return -1;
      }
    }
    return -1;
  }

  /**
   * Check whether a function term in uexp belongs to a function family.
   * That means, the function name is like (familyName + "_" + N) for some non-negative integer N.
   */
  public static boolean belongsToFamily(UFunc func, String familyName) {
    String funcName = func.funcName().toString();
    int size = func.subTerms().size();
    int argCount = PredefinedFunctions.parseArgCount(funcName, familyName);
    return argCount >= 0 && argCount == size;
  }

}

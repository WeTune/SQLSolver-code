package wtune.superopt.uexpr;

public class PredefinedFunctions {

  public static final String NAME_LIKE = "like_op";
  public static final String NAME_IN_LIST = "in_list";

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

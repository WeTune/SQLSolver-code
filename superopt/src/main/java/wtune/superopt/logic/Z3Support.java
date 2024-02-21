package wtune.superopt.logic;

import com.microsoft.z3.*;
import wtune.common.utils.SetSupport;
import wtune.superopt.liastar.LiaStar;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class Z3Support {
  /**
   * Add var definitions and non-negativity to a Z3 context. It also updates the var definition map.
   * Vars already in the map are ignored.
   *
   * @return the non-negativity constraint of vars
   */
  public static BoolExpr defineNonNegativeVars(
          Context ctx,
          Map<String, IntExpr> varDef,
          Iterable<String> vars) {
    return defineNonNegativeVarsWithLimit(ctx, varDef, vars, 0);
  }

  /**
   * Add var definitions and non-negativity to a Z3 context. It also updates the var definition map.
   * Vars already in the map are ignored.
   *
   * @param limit if positive, the upper bound of dimensions of vars
   * @return the non-negativity constraint of vars
   */
  public static BoolExpr defineNonNegativeVarsWithLimit(
          Context ctx,
          Map<String, IntExpr> varDef,
          Iterable<String> vars,
          int limit) {
    BoolExpr constraint = ctx.mkBool(true);
    for (String var : vars) {
      if (!varDef.containsKey(var)) {
        // for each undefined var
        // create its definition
        IntExpr varExp = ctx.mkIntConst(var);
        varDef.put(var, varExp);
        // and its non-negativity constraint
        BoolExpr nonNeg = ctx.mkLe(ctx.mkInt(0), varExp);
        constraint = ctx.mkAnd(constraint, nonNeg);
        if (limit > 0) {
          BoolExpr withLimit = ctx.mkLe(varExp, ctx.mkInt(limit));
          constraint = ctx.mkAnd(constraint, withLimit);
        }
      }
    }
    return constraint;
  }

  public static boolean isValidLia(LiaStar lia, Set<String> universalBVs) {
    return isValidLia(lia, universalBVs, false);
  }
  /**
   * Check whether a LIA formula is always true. Note that all variables are assumed to be
   * non-negative.
   *
   * @param lia the LIA formula to check
   * @param universalBVs the vars bound by "forall"
   * @return whether the LIA formula "forall universalBVs >= 0. (exists ... >= 0). lia" is valid
   *     (i.e. always true); the "exists" part covers free vars in lia except universalBVs.
   */
  public static boolean isValidLia(LiaStar lia, Set<String> universalBVs, boolean log) {
    // Since LIA does not contain forall/exists,
    // let FVs in universalBVs be bound by "forall",
    // and other FVs be bound by "exists"
    Set<String> existBVs = SetSupport.minus(lia.collectVarSet(), universalBVs);
    // validity of "forall universalBVs. universalBVs >= 0 -> exists existBVs. existBVs >= 0 /\ lia"
    // is reduced to falsity of
    // "exists universalBVs. universalBVs >= 0 /\ forall existBVs. existBVs >= 0 -> not lia",
    // or unsatisfiability of
    // "universalBVs >= 0 /\ forall existBVs. existBVs >= 0 -> not lia"
    try (final Context ctx = new Context()) {
      Map<String, IntExpr> varDef = new HashMap<>();
      BoolExpr nnEx = defineNonNegativeVars(ctx, varDef, existBVs);
      BoolExpr nnUn = defineNonNegativeVars(ctx, varDef, universalBVs);
      Map<String, FuncDecl> funcDef = new HashMap<>();
      BoolExpr notLia = ctx.mkNot((BoolExpr) lia.transToSMT(ctx, varDef, funcDef));
      BoolExpr body;
      if (existBVs.isEmpty()) {
        body = notLia;
      } else {
        body = ctx.mkForall(
                existBVs.stream().map(varDef::get).toList().toArray(new Expr[0]),
                ctx.mkImplies(nnEx, notLia),
                0,
                null,
                null,
                null,
                null);
      }
      BoolExpr toCheck = ctx.mkAnd(nnUn, body);
      // function properties
      /*for (FuncDecl func : funcDef.values()) {
        Expr[] args = new Expr[func.getArity()];
        for (int i = 0; i < args.length; i++) {
          args[i] = ctx.mkIntConst("x" + i);
        }
        BoolExpr funcNNBody = ctx.mkLe(ctx.mkInt(0), ctx.mkApp(func, args));
        BoolExpr funcNN = ctx.mkForall(args, funcNNBody, 0, null, null, null, null);
        toCheck = ctx.mkAnd(funcNN, toCheck);
      }*/
      // solve
      if (log) {
        System.out.println("check validity: ");
        System.out.println(toCheck);
      }
      Solver s = ctx.mkSolver(ctx.tryFor(ctx.mkTactic("lia"), SqlSolver.timeout));
      s.add(toCheck);
      Status q = s.check();
      return q == Status.UNSATISFIABLE;
    }
  }
}

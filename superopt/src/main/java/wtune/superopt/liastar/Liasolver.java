package wtune.superopt.liastar;

import com.microsoft.z3.*;
import wtune.superopt.logic.LogicSupport;
import wtune.superopt.logic.SqlSolver;

import java.util.*;
import static wtune.superopt.liastar.Liastar.*;

public class Liasolver {

  Liastar liaFormula;

  public Liasolver(Liastar f) {
    liaFormula = f;
  }

  Liasolver(Liastar f, long m) {
    liaFormula = f;
  }

  public LiaSolverStatus solve() {
    try {
      String result = checkUnderapp();
      if (result.equals("SAT")) return LiaSolverStatus.SAT;
    } catch (Exception e) {
    }

//    try {
//      String result = checkOverOverapp();
//      if (result.equals("UNSAT")) return LiaSolverStatus.UNSAT;
//    } catch (Exception e) {
//    }

    try {
      String result = checkOverapp();
      if (result.equals("UNSAT")) return LiaSolverStatus.UNSAT;
      if (result.equals("SAT")) return LiaSolverStatus.SAT;
      return LiaSolverStatus.UNKNOWN;
    } catch (Exception e) {
      if (LogicSupport.dumpLiaFormulas) {
        e.printStackTrace();
      }
      return LiaSolverStatus.UNKNOWN;
    }

  }

  String checkUnderapp() {
    try {
      Liastar curexp = liaFormula.deepcopy();
      curexp = expandStarWithUnderapp(curexp, 2);
      return solveLia(curexp);
    } catch (Exception e) {
      return "UNKNOWN";
    }
  }

  String checkOverOverapp() throws Exception {
    Liastar tmpFormula = liaFormula.deepcopy();
    tmpFormula = tmpFormula.subformulaWithoutStar();
    String result = solveLia(tmpFormula);
    return result;
  }

  String checkOverapp() throws Exception {
    if (LogicSupport.dumpLiaFormulas)
      System.out.println("init: " + liaFormula);

    Liastar tmpFormula = liaFormula.deepcopy();
    tmpFormula = tmpFormula.pushUpParameter(new HashSet<>());
    tmpFormula = tmpFormula.removeParameter();
    if (LogicSupport.dumpLiaFormulas)
      System.out.println("remove param: " + tmpFormula);

    tmpFormula.simplifyMult(new HashMap<>());
    tmpFormula.mergeMult(new HashMap<>());
    if (LogicSupport.dumpLiaFormulas)
      System.out.println("remove multiplication: " + tmpFormula);

    String result = solveNestedLiastar(tmpFormula);

    if (!result.equals("UNSAT")) {
      tmpFormula = liaFormula.deepcopy();
      tmpFormula = tmpFormula.pushUpParameter(new HashSet<>());
      tmpFormula = tmpFormula.mergeSameVars();
      tmpFormula = tmpFormula.removeParameterEager();
      if (LogicSupport.dumpLiaFormulas)
        System.out.println("eager remove param: " + tmpFormula);

      tmpFormula.simplifyMult(new HashMap<>());
      tmpFormula.mergeMult(new HashMap<>());
      if (LogicSupport.dumpLiaFormulas)
        System.out.println("remove multiplication: " + tmpFormula);

      return solveNestedLiastar(tmpFormula);
    } else {
      return "UNSAT";
    }
  }

  String solveLia(Liastar f) {
    try (final Context ctx = new Context()) {
      BoolExpr target = ctx.mkTrue();

      Set<String> varsName = f.collectVarSet();
      HashMap<String, IntExpr> varDef = new HashMap<>();
      for (String varName : varsName) {
        IntExpr varExp = ctx.mkIntConst(varName);
        varDef.put(varName, varExp);
        target = ctx.mkAnd(target, ctx.mkLe(ctx.mkInt(0), varExp));
      }

      target = ctx.mkAnd(target, (BoolExpr) f.transToSMT(ctx, varDef));
      if (LogicSupport.dumpLiaFormulas) {
        System.out.println("FOL: " + target.toString());
      }

      Solver s = (f.toString().contains("sqrt")) ?
          ctx.mkSolver() :
          ctx.mkSolver(ctx.tryFor(ctx.mkTactic("qflia"), SqlSolver.timeout));
//       Solver s = ctx.mkSolver();
      s.add(target);
      Status q = s.check();
      if (LogicSupport.dumpLiaFormulas) {
        System.out.println("smt solver: " + q.toString());
      }
      return switch (q) {
        case UNKNOWN -> "UNKNOWN";
        case SATISFIABLE -> "SAT";
        case UNSATISFIABLE -> "UNSAT";
      };
    }
  }

  String solveNestedLiastar(Liastar f) throws Exception {
    if (LogicSupport.dumpLiaFormulas)
      System.out.println("liastar: " + f.toString());
    f.expandStar();
    f = f.simplifyIte();

    if (LogicSupport.dumpLiaFormulas) {
      System.out.println("lia: " + f.toString());
      System.out.println("#variables in LIA without *: " + f.getVars().size());
    }

    return solveLia(f);
  }


  String checkOverappWithK() {
    Liastar tmpFormula = liaFormula.deepcopy();
    tmpFormula.simplifyMult(new HashMap<>());
    tmpFormula.mergeMult(new HashMap<>());

    try {
      Status s = solveWithK(tmpFormula);
      if (s == Status.UNSATISFIABLE) return "UNSAT";
    } catch (Exception e) {

    }
    while(true);
  }

  Status solveWithK(Liastar e) {
    Set<String> vars = e.collectVarSet();
    Context ctx = new Context();
    Solver sol = ctx.mkSolver();
    for (String var : vars) {
      sol.add(ctx.mkGe(ctx.mkIntConst(var), ctx.mkInt(0)));
    }
    Expr expr = e.expandStarWithK(ctx, sol, "");
    Status status = sol.check(expr);
    return status;
  }

}

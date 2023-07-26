package wtune.superopt.lia;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import org.junit.jupiter.api.Test;
import wtune.superopt.liastar.Liastar;
import wtune.superopt.logic.SqlSolver;
import wtune.superopt.logic.SqlSolverSupport;
import wtune.superopt.substitution.Substitution;
import wtune.superopt.substitution.SubstitutionBank;
import wtune.superopt.substitution.SubstitutionSupport;
import wtune.superopt.uexpr.*;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static wtune.superopt.TestHelper.dataDir;
import static wtune.superopt.uexpr.UPred.PredKind.EQ;

class LiaFunctionalityTest {

  Status solveWithK(Liastar e) {
    Set<String> vars = e.collectVarSet();
    Context ctx = new Context();
    Solver sol = ctx.mkSolver();
    for (String var : vars) {
      sol.add(ctx.mkGe(ctx.mkIntConst(var), ctx.mkInt(0)));
    }
    Expr expr = e.expandStarWithK(ctx, sol, "");
    Status status = sol.check(expr);
    System.out.println(status);

//    if (status == Status.SATISFIABLE) {
//      Model model = sol.getModel();
//      System.out.printf("u1 = %s u2 = %s\n",
//              model.eval(ctx.mkIntConst("u1"), false),
//              model.eval(ctx.mkIntConst("u2"), false)
//      );
//    }

    return status;
  }

  @Test
  void testExpandWithK() {
    // u1 != u2 /\ (u1, u2) in { (x1, x2) | x1 = x2 }*
    Liastar e1 = Liastar.mkAnd(false,
            Liastar.mkNot(false,
                    Liastar.mkEq(false,
                            Liastar.mkVar(false, "u1"),
                            Liastar.mkVar(false, "u2")
                    )
            ),
            Liastar.mkSum(false,
                    new ArrayList(List.of("u1", "u2")),
                    new ArrayList(List.of("x1", "x2")),
                    Liastar.mkEq(true,
                            Liastar.mkVar(true, "x1"),
                            Liastar.mkVar(true, "x2")
                    )
            )
    );
    assert(solveWithK(e1) == Status.UNSATISFIABLE);

    // u1 != u2 /\ (u1, u2) in { (x1, x2) |
    //                      (x1, x2) in { (y1, y2) | y1 = y2 }*
    //                                       }*
    Liastar e2 = Liastar.mkAnd(false,
            Liastar.mkNot(false,
                    Liastar.mkEq(false,
                            Liastar.mkVar(false, "u1"),
                            Liastar.mkVar(false, "u2")
                    )
            ),
            Liastar.mkSum(false,
                    new ArrayList(List.of("u1", "u2")),
                    new ArrayList(List.of("x1", "x2")),
                    Liastar.mkSum(true,
                            new ArrayList(List.of("x1", "x2")),
                            new ArrayList(List.of("y1", "y2")),
                            Liastar.mkEq(true,
                                    Liastar.mkVar(true, "y1"),
                                    Liastar.mkVar(true, "y2")
                            )
                    )
            )
    );
    assert(solveWithK(e2) == Status.UNSATISFIABLE);

    // ite(v1 > 0, 1, 0) != ite(v2 + v3 > 0, 1, 0)
    // /\ (v1, v2, v3, v4, v5) in { (x1, x2, x3, x4, x5) |
    //                              (x4 = 0 \/ x4 = 1) /\ (x5 = 0 \/ x5 = 1)
    //                              /\ x1 = ite(x4 = 1, x5, 0) /\ x2 = ite(x4 = 1, x5, 0) /\ x3 = ite(x4 = 1, x5, 0) }*
    Liastar e3 = Liastar.mkAnd(false,
            Liastar.mkNot(false, Liastar.mkEq(false,
                    Liastar.mkIte(false,
                            Liastar.mkLt(false, Liastar.mkConst(false, 0), Liastar.mkVar(false, "v1")),
                            Liastar.mkConst(false, 1), Liastar.mkConst(false, 0)
                    ),
                    Liastar.mkIte(false,
                            Liastar.mkLt(false,
                                    Liastar.mkConst(false, 0),
                                    Liastar.mkPlus(false,
                                            Liastar.mkVar(false, "v2"),
                                            Liastar.mkVar(false, "v3")
                                    )
                            ),
                            Liastar.mkConst(false, 1), Liastar.mkConst(false, 0)
                    )
            )),
            Liastar.mkSum(false,
                    new ArrayList(List.of("v1", "v2", "v3", "v4", "v5")),
                    new ArrayList(List.of("x1", "x2", "x3", "x4", "x5")),
                    Liastar.mkAnd(true,
                            Liastar.mkOr(true,
                                    Liastar.mkEq(true, Liastar.mkVar(true, "x4"), Liastar.mkConst(true, 0)),
                                    Liastar.mkEq(true, Liastar.mkVar(true, "x4"), Liastar.mkConst(true, 1))
                            ),
                            Liastar.mkAnd(true,
                                    Liastar.mkOr(true,
                                            Liastar.mkEq(true, Liastar.mkVar(true, "x5"), Liastar.mkConst(true, 0)),
                                            Liastar.mkEq(true, Liastar.mkVar(true, "x5"), Liastar.mkConst(true, 1))
                                    ),
                                    Liastar.mkAnd(true,
                                            Liastar.mkEq(true,
                                                    Liastar.mkVar(true, "x1"),
                                                    Liastar.mkIte(true,
                                                            Liastar.mkEq(true, Liastar.mkVar(true, "x4"), Liastar.mkConst(true, 1)),
                                                            Liastar.mkVar(true, "x5"),
                                                            Liastar.mkConst(true, 0)
                                                    )
                                            ),
                                            Liastar.mkAnd(true,
                                                    Liastar.mkEq(true,
                                                            Liastar.mkVar(true, "x2"),
                                                            Liastar.mkIte(true,
                                                                    Liastar.mkEq(true, Liastar.mkVar(true, "x4"), Liastar.mkConst(true, 1)),
                                                                    Liastar.mkVar(true, "x5"),
                                                                    Liastar.mkConst(true, 0)
                                                            )
                                                    ),
                                                    Liastar.mkEq(true,
                                                            Liastar.mkVar(true, "x3"),
                                                            Liastar.mkIte(true,
                                                                    Liastar.mkEq(true, Liastar.mkVar(true, "x4"), Liastar.mkConst(true, 1)),
                                                                    Liastar.mkVar(true, "x5"),
                                                                    Liastar.mkConst(true, 0)
                                                            )
                                                    )
                                            )
                                   )
                            )
                    )
            )
    );
    assert(solveWithK(e3) == Status.UNSATISFIABLE);
  }

//  @Test
//  void testDNF() throws IOException {
//    final Path ruleFilePath = dataDir().resolve("prepared").resolve("rules.example.txt");
//    final SubstitutionBank rules = SubstitutionSupport.loadBank(ruleFilePath);
//    int targetId = 32;
//    for (Substitution rule : rules.rules()) {
//      if (rule.id() > 32) break;
//      if (rule.id() > targetId) continue;
//      final UExprTranslationResult uExprs =
//          UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
//      UTerm query1 = uExprs.sourceExpr(), query2 = uExprs.targetExpr();
//      query1 = UExprSupport.normalizeExprEnhance(query1);
//      query2 = UExprSupport.normalizeExprEnhance(query2);
//      SqlSolverSupport translator = new SqlSolverSupport(query1, query2, uExprs.sourceOutVar());
//      Liastar fstar = translator.uexpToLiastar();
//      System.out.println(Liastar.paramLiaStar2DNF(fstar, false));
//      break;
//    }
//  }

//  @Test
//  void testSimpleDNF() {
//    // e /\ (a = ite(b, c, d) \/ f)
//    final Liastar a = Liastar.mkVar(false, "a");
//    final Liastar b = Liastar.mkVar(false, "b");
//    final Liastar c = Liastar.mkVar(false, "c");
//    final Liastar d = Liastar.mkVar(false, "d");
//    final Liastar e = Liastar.mkVar(false, "e");
//    final Liastar f = Liastar.mkVar(false, "f");
//    final Liastar ite = Liastar.mkIte(false, b, c, d);
//    final Liastar subEq = Liastar.mkEq(false, a, ite);
//    final Liastar subOr = Liastar.mkOr(false, subEq, f);
//    final Liastar subAnd = Liastar.mkAnd(false, e, subOr);
//    System.out.println(Liastar.paramLiaStar2DNF(subAnd, true));
//  }
}

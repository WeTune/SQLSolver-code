package wtune.superopt.lia;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import org.junit.jupiter.api.Test;
import wtune.superopt.liastar.LiaStar;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

class LiaFunctionalityTest {

  Status solveWithK(LiaStar e) {
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
    LiaStar e1 = LiaStar.mkAnd(false,
            LiaStar.mkNot(false,
                    LiaStar.mkEq(false,
                            LiaStar.mkVar(false, "u1"),
                            LiaStar.mkVar(false, "u2")
                    )
            ),
            LiaStar.mkSum(false,
                    new ArrayList(List.of("u1", "u2")),
                    new ArrayList(List.of("x1", "x2")),
                    LiaStar.mkEq(true,
                            LiaStar.mkVar(true, "x1"),
                            LiaStar.mkVar(true, "x2")
                    )
            )
    );
    assert(solveWithK(e1) == Status.UNSATISFIABLE);

    // u1 != u2 /\ (u1, u2) in { (x1, x2) |
    //                      (x1, x2) in { (y1, y2) | y1 = y2 }*
    //                                       }*
    LiaStar e2 = LiaStar.mkAnd(false,
            LiaStar.mkNot(false,
                    LiaStar.mkEq(false,
                            LiaStar.mkVar(false, "u1"),
                            LiaStar.mkVar(false, "u2")
                    )
            ),
            LiaStar.mkSum(false,
                    new ArrayList(List.of("u1", "u2")),
                    new ArrayList(List.of("x1", "x2")),
                    LiaStar.mkSum(true,
                            new ArrayList(List.of("x1", "x2")),
                            new ArrayList(List.of("y1", "y2")),
                            LiaStar.mkEq(true,
                                    LiaStar.mkVar(true, "y1"),
                                    LiaStar.mkVar(true, "y2")
                            )
                    )
            )
    );
    assert(solveWithK(e2) == Status.UNSATISFIABLE);

    // ite(v1 > 0, 1, 0) != ite(v2 + v3 > 0, 1, 0)
    // /\ (v1, v2, v3, v4, v5) in { (x1, x2, x3, x4, x5) |
    //                              (x4 = 0 \/ x4 = 1) /\ (x5 = 0 \/ x5 = 1)
    //                              /\ x1 = ite(x4 = 1, x5, 0) /\ x2 = ite(x4 = 1, x5, 0) /\ x3 = ite(x4 = 1, x5, 0) }*
    LiaStar e3 = LiaStar.mkAnd(false,
            LiaStar.mkNot(false, LiaStar.mkEq(false,
                    LiaStar.mkIte(false,
                            LiaStar.mkLt(false, LiaStar.mkConst(false, 0), LiaStar.mkVar(false, "v1")),
                            LiaStar.mkConst(false, 1), LiaStar.mkConst(false, 0)
                    ),
                    LiaStar.mkIte(false,
                            LiaStar.mkLt(false,
                                    LiaStar.mkConst(false, 0),
                                    LiaStar.mkPlus(false,
                                            LiaStar.mkVar(false, "v2"),
                                            LiaStar.mkVar(false, "v3")
                                    )
                            ),
                            LiaStar.mkConst(false, 1), LiaStar.mkConst(false, 0)
                    )
            )),
            LiaStar.mkSum(false,
                    new ArrayList(List.of("v1", "v2", "v3", "v4", "v5")),
                    new ArrayList(List.of("x1", "x2", "x3", "x4", "x5")),
                    LiaStar.mkAnd(true,
                            LiaStar.mkOr(true,
                                    LiaStar.mkEq(true, LiaStar.mkVar(true, "x4"), LiaStar.mkConst(true, 0)),
                                    LiaStar.mkEq(true, LiaStar.mkVar(true, "x4"), LiaStar.mkConst(true, 1))
                            ),
                            LiaStar.mkAnd(true,
                                    LiaStar.mkOr(true,
                                            LiaStar.mkEq(true, LiaStar.mkVar(true, "x5"), LiaStar.mkConst(true, 0)),
                                            LiaStar.mkEq(true, LiaStar.mkVar(true, "x5"), LiaStar.mkConst(true, 1))
                                    ),
                                    LiaStar.mkAnd(true,
                                            LiaStar.mkEq(true,
                                                    LiaStar.mkVar(true, "x1"),
                                                    LiaStar.mkIte(true,
                                                            LiaStar.mkEq(true, LiaStar.mkVar(true, "x4"), LiaStar.mkConst(true, 1)),
                                                            LiaStar.mkVar(true, "x5"),
                                                            LiaStar.mkConst(true, 0)
                                                    )
                                            ),
                                            LiaStar.mkAnd(true,
                                                    LiaStar.mkEq(true,
                                                            LiaStar.mkVar(true, "x2"),
                                                            LiaStar.mkIte(true,
                                                                    LiaStar.mkEq(true, LiaStar.mkVar(true, "x4"), LiaStar.mkConst(true, 1)),
                                                                    LiaStar.mkVar(true, "x5"),
                                                                    LiaStar.mkConst(true, 0)
                                                            )
                                                    ),
                                                    LiaStar.mkEq(true,
                                                            LiaStar.mkVar(true, "x3"),
                                                            LiaStar.mkIte(true,
                                                                    LiaStar.mkEq(true, LiaStar.mkVar(true, "x4"), LiaStar.mkConst(true, 1)),
                                                                    LiaStar.mkVar(true, "x5"),
                                                                    LiaStar.mkConst(true, 0)
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

package wtune.superopt.logic;

import com.microsoft.z3.Context;
import com.microsoft.z3.Global;
import wtune.sql.plan.PlanContext;
import wtune.sql.plan.PlanKind;
import wtune.superopt.fragment.Agg;
import wtune.superopt.fragment.AggFuncKind;
import wtune.superopt.fragment.Symbol;
import wtune.superopt.nodetrans.SPESSupport;
import wtune.superopt.substitution.Substitution;
import wtune.superopt.substitution.SubstitutionSupport;
import wtune.superopt.substitution.SubstitutionTranslatorResult;
import wtune.superopt.uexpr.*;
import wtune.superopt.uexpr.normalizer.QueryUExprICRewriter;

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;

import static wtune.common.utils.IterableSupport.all;
import static wtune.common.utils.IterableSupport.any;
import static wtune.sql.plan.PlanSupport.hasNodeOfKind;

public abstract class LogicSupport {
  static {
//    final String timeout = System.getProperty("wetune.smt_timeout", "20");
    Global.setParameter("smt.random_seed", "9876543210");
    Global.setParameter("smt.qi.quick_checker", "2");
    Global.setParameter("smt.qi.max_multi_patterns", "1024");
    Global.setParameter("smt.mbqi.max_iterations", "3");
    Global.setParameter("timeout", SqlSolver.timeout.toString());
    Global.setParameter("combined_solver.solver2_unknown", "0");
    Global.setParameter("pp.max_depth", "100");
  }

  public static final int EQ = 0, NEQ = -1, UNKNOWN = 1, FAST_REJECTED = -2;
  private static final AtomicInteger NUM_INVOCATIONS = new AtomicInteger(0);
  public static boolean dumpFormulas;
  public static boolean dumpLiaFormulas;

  public static final int PROVER_DISABLE_INTEGRITY_CONSTRAINTS_THEOREM = 1;

  private LogicSupport() {
  }

  static void incrementNumInvocations() {
    NUM_INVOCATIONS.incrementAndGet();
  }

  public static void setDumpFormulas(boolean dumpFormulas) {
    LogicSupport.dumpFormulas = dumpFormulas;
  }

  public static void setDumpLiaFormulas(boolean dumpLiaFormulas) {
    LogicSupport.dumpLiaFormulas = dumpLiaFormulas;
  }

  public static String stringifyResult(int result) {
    return switch (result) {
      case EQ -> "EQ";
      case NEQ -> "NEQ";
      case UNKNOWN -> "UNKNOWN";
      case FAST_REJECTED -> "FAST_REJECTED";
      default -> "??";
    };
  }

  public static int numInvocations() {
    return NUM_INVOCATIONS.get();
  }

  public static int proveEq(UExprTranslationResult uExprs) {
    try (final Context z3 = new Context()) {
      return new LogicProver(uExprs, z3, 0).proveEq();
    }
  }

  public static int proveEqNotNeedLia(UExprTranslationResult uExprs) {
    try (final Context z3 = new Context()) {
      return new LogicProver(uExprs, z3, 0).proveEqNotNeedLia();
    }
  }

  public static int proveEq(UExprTranslationResult uExprs, int tweaks) {
    try (final Context z3 = new Context()) {
      return new LogicProver(uExprs, z3, tweaks).proveEq();
    }
  }

  public static int proveEqBySpes(Substitution rule) {
    try {
      var planPair = SubstitutionSupport.translateAsPlan2(rule);
      boolean eq = SPESSupport.prove(planPair.getLeft(), planPair.getRight());
      return eq ? EQ : NEQ;
    } catch (Exception e) {
      return NEQ;
    }
  }

  public static int proveEqByLIAStar(UExprTranslationResult uExprs) {
    try {
      return new SqlSolver(uExprs).proveEq();
    } catch (Exception e) {
      e.printStackTrace();
      return UNKNOWN;
    }
  }

  public static int proveEqByLIAStar(UExprConcreteTranslationResult uExprs) {
    try {
      return new SqlSolver(uExprs).proveEq();
    } catch (Exception e) {
      e.printStackTrace();
      return UNKNOWN;
    }
  }

  public static int proveEqByLIAStar(Substitution rule) {
    return proveEqByLIAStar(rule, null, false);
  }

  public static int proveEqByLIAStar(
      Substitution rule,
      SubstitutionTranslatorResult extraInfo,
      boolean isConcretePlan) {
    try {
      int flag = UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE;
      if (isConcretePlan) flag |= UExprSupport.UEXPR_FLAG_VERIFY_CONCRETE_PLAN;

      final UExprTranslationResult uExprs = UExprSupport.translateToUExpr(rule, flag, extraInfo);
      if (uExprs == null) return UNKNOWN;
      return new SqlSolver(uExprs).proveEq();
    } catch (Exception e) {
      e.printStackTrace();
      return UNKNOWN;
    }
  }

  public static int proveEqByLIAStar2(Substitution rule) {
    return proveEqByLIAStar2(rule, null, false);
  }

  public static int proveEqByLIAStar2(
      Substitution rule,
      SubstitutionTranslatorResult extraInfo,
      boolean isConcretePlan) {
    if (isConcretePlan) assert extraInfo != null;

    try {
      final List<Symbol> srcFuncSymbols = rule._0().symbols().symbolsOf(Symbol.Kind.FUNC);
      final List<Symbol> tgtFuncSymbols = rule._1().symbols().symbolsOf(Symbol.Kind.FUNC);
      // Rules without Agg nodes
      if (srcFuncSymbols.isEmpty() && tgtFuncSymbols.isEmpty())
        return proveEqByLIAStar(rule, extraInfo, isConcretePlan);
      // Concrete queries with deterministic Agg functions, no need to enum all cases
      if (all(srcFuncSymbols, f -> ((Agg) rule._0().symbols().ownerOf(f)).aggFuncKind() != AggFuncKind.UNKNOWN) &&
          all(tgtFuncSymbols, f -> ((Agg) rule._1().symbols().ownerOf(f)).aggFuncKind() != AggFuncKind.UNKNOWN))
        return proveEqByLIAStar(rule, extraInfo, isConcretePlan);

      // For UNKNOWN type Agg function: enumerate all cases of agg functions on each Agg node
      final Set<Symbol> visitedFuncSymbols = new HashSet<>();
      final Map<Set<Symbol>, List<AggFuncKind>> feasibleFuncMap = new HashMap<>();
      for (Symbol fSym : srcFuncSymbols) {
        if (visitedFuncSymbols.contains(fSym)) continue;
        final Set<Symbol> eqFuncSyms = new HashSet<>(rule.constraints().eqClassOf(fSym));
        for (Symbol tgtFuncSym : tgtFuncSymbols) {
          if (any(eqFuncSyms, s -> rule.constraints().instantiationOf(tgtFuncSym) == s))
            eqFuncSyms.add(tgtFuncSym);
        }
        if (any(eqFuncSyms, s -> ((Agg) s.ctx().ownerOf(s)).deduplicated()))
          feasibleFuncMap.put(eqFuncSyms, AggFuncKind.dedupAggFuncKinds);
        else feasibleFuncMap.put(eqFuncSyms, AggFuncKind.commonAggFuncKinds);
        visitedFuncSymbols.addAll(eqFuncSyms);
      }

      final List<Set<Symbol>> eqFuncSymList = feasibleFuncMap.keySet().stream().toList();
      return enumAggFunc(rule, extraInfo, isConcretePlan, eqFuncSymList, feasibleFuncMap, 0);
    } catch (Exception e) {
      e.printStackTrace();
      return UNKNOWN;
    }
  }

  private static int enumAggFunc(
      Substitution rule,
      SubstitutionTranslatorResult extraInfo,
      boolean isConcretePlan,
      List<Set<Symbol>> eqFuncSymList,
      Map<Set<Symbol>, List<AggFuncKind>> feasibleFuncMap,
      int index) {
    if (index == eqFuncSymList.size()) return proveEqByLIAStar(rule, extraInfo, isConcretePlan);

    final Set<Symbol> eqFuncSyms = eqFuncSymList.get(index);
    int res;
    for (AggFuncKind aggFuncKind : feasibleFuncMap.get(eqFuncSyms)) {
      for (Symbol funcSym : eqFuncSyms) {
        ((Agg) funcSym.ctx().ownerOf(funcSym)).setAggFuncKind(aggFuncKind);
      }
      res = enumAggFunc(rule, extraInfo, isConcretePlan, eqFuncSymList, feasibleFuncMap, index + 1);
      for (Symbol funcSym : eqFuncSyms) {
        ((Agg) funcSym.ctx().ownerOf(funcSym)).setAggFuncKind(AggFuncKind.UNKNOWN);
      }
      if (res != EQ) return res;
    }
    return EQ;
  }

  public static int proveEqByLIAStarSymbolic(PlanContext p0, PlanContext p1) {
    if (!CASTSupport.castHandler(p0, p1)) {
      return NEQ;
    }

    if (!hasNodeOfKind(p0, PlanKind.Sort) && !hasNodeOfKind(p0, PlanKind.Limit) &&
        !hasNodeOfKind(p1, PlanKind.Sort) && !hasNodeOfKind(p1, PlanKind.Limit)) {
      final SubstitutionTranslatorResult res0 = SubstitutionSupport.translateAsSubstitution(p0, p1);
      if (res0.rule() == null) return LogicSupport.UNKNOWN;

      return LogicSupport.proveEqByLIAStar2(res0.rule(), res0, true);
    }

    HashSet<SubstitutionTranslatorResult> results = OrderbySupport.sortHandler(p0, p1);
    if (results == null) return UNKNOWN;

    for (SubstitutionTranslatorResult res : results) {
      int verifyResult = LogicSupport.proveEqByLIAStar2(res.rule(), res, true);
      if (verifyResult != EQ) return verifyResult;
    }
    return LogicSupport.EQ;
  }

  private static int proveEqByLIAStarSelectedIC(PlanContext p0, PlanContext p1,
                                                int extraFlags) {
    int selectedIC = 0;
    do {
      QueryUExprICRewriter.selectIC(selectedIC);
      final UExprConcreteTranslationResult uExprsWithICRewrite =
          UExprSupport.translateQueryToUExpr(p0, p1,
                  UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE
                          | extraFlags);
      if (uExprsWithICRewrite != null) {
        final int res1 = LogicSupport.proveEqByLIAStar(uExprsWithICRewrite);
        if (res1 == EQ) {
          QueryUExprICRewriter.selectIC(-1);
          return res1;
        }
      }
      selectedIC = selectedIC + 1;
    } while (QueryUExprICRewriter.hasIC());
    QueryUExprICRewriter.selectIC(-1);
    return NEQ;
  }

  private static int proveEqByLIAStarConcreteNoSortWithIC(PlanContext p0, PlanContext p1, int extraFlags) {
    final UExprConcreteTranslationResult uExprsWithIC =
            UExprSupport.translateQueryToUExpr(p0, p1,
                    UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE
                            | extraFlags);
    if (uExprsWithIC != null) {
      final int res1 = LogicSupport.proveEqByLIAStar(uExprsWithIC);
      if (res1 == EQ) return EQ;
      if (proveEqByLIAStarSelectedIC(p0, p1, extraFlags) == EQ) return EQ;
    }
    return (uExprsWithIC == null) ? UNKNOWN : NEQ;
  }

  private static int proveEqByLIAStarConcreteNoSort(PlanContext p0, PlanContext p1) {
    int resICUnexplainedPred = proveEqByLIAStarConcreteNoSortWithIC(p0, p1,
            UExprSupport.UEXPR_FLAG_NO_EXPLAIN_PREDICATES);
    if (resICUnexplainedPred == EQ) return EQ;
    int resIC = proveEqByLIAStarConcreteNoSortWithIC(p0, p1, 0);
    if (resIC == EQ) return EQ;
    final UExprConcreteTranslationResult uExprs = UExprSupport.translateQueryToUExpr(p0, p1, 0);
    if (uExprs != null) {
      final int res0 = LogicSupport.proveEqByLIAStar(uExprs);
      if (res0 == EQ) return EQ;
    }
    return (resICUnexplainedPred == UNKNOWN && resIC == UNKNOWN) ?
            UNKNOWN : NEQ;
  }

  public static int proveEqByLIAStarConcrete(PlanContext p0, PlanContext p1) {
//    System.out.println("Proving\n" + p0 + "\n" + p1);
    if (!CASTSupport.castHandler(p0, p1)) {
      return NEQ;
    }

    if (!hasNodeOfKind(p0, PlanKind.Sort) && !hasNodeOfKind(p1, PlanKind.Sort) ) {
      return proveEqByLIAStarConcreteNoSort(p0, p1);
    }
    HashSet<SubstitutionTranslatorResult> results = OrderbySupport.sortHandler(p0, p1);
    if (results == null) {
      //System.err.println("Complex Order By not support");
      return UNKNOWN;
    }

    for (SubstitutionTranslatorResult res : results) {
      int verifyResult = proveEqByLIAStarConcrete(res.src, res.tgt);
      if (verifyResult != EQ) return verifyResult;
    }
    return LogicSupport.EQ;
  }

  public static boolean isMismatchedOutput(UExprTranslationResult uExprs) {
    // case 1: different output schema
    final UVar sourceOutVar = uExprs.sourceOutVar();
    final UVar targetOutVar = uExprs.targetOutVar();
    final SchemaDesc srcOutSchema = uExprs.schemaOf(sourceOutVar);
    final SchemaDesc tgtOutSchema = uExprs.schemaOf(targetOutVar);
    assert srcOutSchema != null && tgtOutSchema != null;
    return !srcOutSchema.equals(tgtOutSchema);
  }

  public static boolean isMismatchedSummation(UExprTranslationResult uExprs) {
    // cast 2: unaligned variables
    // master: the side with more bounded variables, or the source side if the numbers are equal
    // master: the side with less bounded variables, or the target side if the numbers are equal
    final UTerm srcTerm = uExprs.sourceExpr(), tgtTerm = uExprs.targetExpr();
    final UTerm masterTerm = getMaster(srcTerm, tgtTerm);
    final UTerm slaveTerm = getSlave(srcTerm, tgtTerm);
    return !getBoundedVars(masterTerm).containsAll(getBoundedVars(slaveTerm));
  }

  public static boolean isLatentSummation(UExprTranslationResult uExprs) {
    return containsLatentSummation(getBody(uExprs.sourceExpr()))
        || containsLatentSummation(getBody(uExprs.targetExpr()));
  }

  static boolean containsLatentSummation(UTerm term) {
    // Sum + Sum or Sum * Sum
    final UKind kind = term.kind();
    if (kind == UKind.SUMMATION) return true;
    if (kind == UKind.SQUASH || kind == UKind.NEGATION || kind.isTermAtomic()) return false;
    if (kind == UKind.ADD || kind == UKind.MULTIPLY)
      for (UTerm subTerm : term.subTerms()) {
        if (containsLatentSummation(subTerm)) return true;
      }
    return false;
  }

  static boolean isFastRejected(UExprTranslationResult uExprs) {
    // return isMismatchedOutput(uExprs) || isMismatchedSummation(uExprs) || isLatentSummation(uExprs);
    return isMismatchedOutput(uExprs);
  }

  static Set<UVar> getBoundedVars(UTerm expr) {
    // Returns the summation variables for a summation, otherwise an empty list.
    if (expr.kind() == UKind.SUMMATION) return ((USum) expr).boundedVars();
    else return Collections.emptySet();
  }

  static UTerm getMaster(UTerm e0, UTerm e1) {
    final Set<UVar> vars0 = getBoundedVars(e0);
    final Set<UVar> vars1 = getBoundedVars(e1);
    if (vars0.size() >= vars1.size()) return e0;
    else return e1;
  }

  static UTerm getSlave(UTerm e0, UTerm e1) {
    final Set<UVar> vars0 = getBoundedVars(e0);
    final Set<UVar> vars1 = getBoundedVars(e1);
    if (vars0.size() < vars1.size()) return e0;
    else return e1;
  }

  static UTerm getBody(UTerm expr) {
    if (expr.kind() == UKind.SUMMATION) return ((USum) expr).body();
    else return expr;
  }
}

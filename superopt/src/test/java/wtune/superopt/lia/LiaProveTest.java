package wtune.superopt.lia;

import org.junit.jupiter.api.Test;
import wtune.common.utils.IOSupport;
import wtune.common.utils.IterableSupport;
import wtune.sql.SqlSupport;
import wtune.sql.ast.SqlNode;
import wtune.sql.ast.constants.JoinKind;
import wtune.sql.plan.*;
import wtune.sql.preprocess.CastHandler;
import wtune.sql.schema.Schema;
import wtune.sql.support.action.NormalizationSupport;
import wtune.stmt.App;
import wtune.superopt.logic.CASTSupport;
import wtune.superopt.logic.LogicSupport;
import wtune.superopt.logic.SqlSolver;
import wtune.superopt.substitution.Substitution;
import wtune.superopt.substitution.SubstitutionBank;
import wtune.superopt.substitution.SubstitutionSupport;
import wtune.superopt.uexpr.UExprConcreteTranslationResult;
import wtune.superopt.uexpr.UExprConcreteTranslator;
import wtune.superopt.uexpr.UExprSupport;
import wtune.superopt.uexpr.UExprTranslationResult;
import wtune.superopt.uexpr.normalizar.QueryUExprICRewriter;

import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.*;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.*;
import static wtune.common.datasource.DbSupport.MySQL;
import static wtune.sql.SqlSupport.*;
import static wtune.sql.plan.PlanSupport.*;
import static wtune.superopt.TestHelper.dataDir;
import static wtune.superopt.logic.LogicSupport.*;

public class LiaProveTest {
  @Test
  void testAgg0() {
    final Substitution rule =
        Substitution.parse(
            "Agg<a1 a2 a5 f0 s1 p0>(Proj<a0 s0>(Input<t0>))|" +
                "Agg<a3 a4 a6 f1 s2 p1>(Input<t1>)|" +
                "AttrsSub(a0,t0);AttrsSub(a1,s0);AttrsSub(a2,s0);" +
                "TableEq(t1,t0);AttrsEq(a3,a1);AttrsEq(a4,a2);AttrsEq(a6,a5);" +
                "PredicateEq(p1,p0);SchemaEq(s2,s1);FuncEq(f1,f0)");
    final UExprTranslationResult uExprs =
        UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
    System.out.println("Rewritten UExpressions: ");
    System.out.println("[[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
    System.out.println("[[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
    LogicSupport.setDumpLiaFormulas(true);
    final int result = LogicSupport.proveEqByLIAStar(rule);
    System.out.println(LogicSupport.stringifyResult(result));
    assertEquals(EQ, result, rule.toString());
  }

  @Test
  void testUsefulRule35Modify() {
    final Substitution rule =
        Substitution.parse(
            "Filter<p3 a7>(Agg<a1 a2 a5 f0 s0 p1>(Filter<p0 a0>(Input<t0>)))|" +
                "Filter<p4 a8>(Agg<a3 a4 a6 f1 s1 p2>(Input<t1>))|" +
                "AttrsEq(a0,a1);AttrsEq(a0,a2);AttrsEq(a0,a7);AttrsEq(a1,a2);AttrsEq(a1,a7);AttrsEq(a2,a7);" +
                "AttrsSub(a0,t0);AttrsSub(a1,t0);AttrsSub(a2,t0);AttrsSub(a5,s0);AttrsSub(a7,s0);" +
                "PredicateEq(p0,p3);" +
                "TableEq(t0,t1);AttrsEq(a3,a1);AttrsEq(a4,a2);AttrsEq(a6,a5);AttrsEq(a8,a7);" +
                "PredicateEq(p2,p1);PredicateEq(p4,p3);SchemaEq(s1,s0);FuncEq(f1,f0)");
    final UExprTranslationResult uExprs =
        UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
    System.out.println("Rewritten UExpressions: ");
    System.out.println("[[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
    System.out.println("[[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
    LogicSupport.setDumpLiaFormulas(true);
    final int result = LogicSupport.proveEqByLIAStar(rule);
    System.out.println(LogicSupport.stringifyResult(result));
    // assertEquals(LogicSupport.EQ, result, rule.toString());
  }

  @Test
  void testEnumeratedRules() throws IOException {
    Path ruleFilePath = dataDir().resolve("prepared").resolve("rules.sqlsolver.txt");
    final SubstitutionBank rules = SubstitutionSupport.loadBank(ruleFilePath);
    for (Substitution rule : rules.rules()) {
      final UExprTranslationResult uExprs =
          UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
      final int result = LogicSupport.proveEqByLIAStar2(rule);
      System.out.println("Rule id: " + rule.id() + " is " + LogicSupport.stringifyResult(result));
    }
  }


  @Test
  void testLiaOnUsefulRuleWithAgg() throws IOException {
    final Path ruleFilePath = dataDir().resolve("prepared").resolve("rules.example.txt");
    final SubstitutionBank rules = SubstitutionSupport.loadBank(ruleFilePath);
    int startId = 33;
    for (Substitution rule : rules.rules()) {
      if (rule.id() < startId) continue;
      final UExprTranslationResult uExprs =
          UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
      final int result = LogicSupport.proveEqByLIAStar2(rule);
      System.out.println("Rule id: " + rule.id() + " is " + LogicSupport.stringifyResult(result));
    }

  }

  @Test
  void testLiaOnUsefulRule() throws IOException {
    final Path ruleFilePath = dataDir().resolve("prepared").resolve("rules.example.txt");
    final SubstitutionBank rules = SubstitutionSupport.loadBank(ruleFilePath);
    int targetId = -1;
    for (Substitution rule : rules.rules()) {
      if (targetId > 0 && rule.id() != targetId) continue;
      final UExprTranslationResult uExprs =
          UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
      if (targetId > 0)
        LogicSupport.setDumpLiaFormulas(true);
      int result = 0;
      if (rule.id() <= 32)
        result = LogicSupport.proveEqByLIAStar(rule);
      else
        result = LogicSupport.proveEqByLIAStar2(rule);
      System.out.println("Rule id: " + rule.id() + " is " + LogicSupport.stringifyResult(result));
    }
  }

  @Test
  void testLiaOnAllWeTuneRules() throws IOException {
    final Path ruleFilePath = dataDir().resolve("prepared").resolve("rules.txt");
    final SubstitutionBank rules = SubstitutionSupport.loadBank(ruleFilePath);
    int targetId = -1;
    for (Substitution rule : rules.rules()) {
      if (targetId > 0 && rule.id() != targetId) continue;
      final UExprTranslationResult uExprs =
          UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
      if (targetId > 0) {
        System.out.println("Rewritten UExpressions: ");
        System.out.println("[[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
        System.out.println("[[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
        LogicSupport.setDumpLiaFormulas(true);
      }
      final int result = LogicSupport.proveEqByLIAStar(rule);
      System.out.println("Rule id: " + rule.id() + " is " + LogicSupport.stringifyResult(result));
    }
  }

  @Test
  void testLiaOnAllSPESRules() throws IOException {
    final Path ruleFilePath = dataDir().resolve("prepared").resolve("rules.spes.prune.txt");
    final SubstitutionBank rules = SubstitutionSupport.loadBank(ruleFilePath);
    int targetId = -1;
    int startId = -1;
    for (Substitution rule : rules.rules()) {
      if (targetId > 0 && rule.id() != targetId) continue;
      if (targetId < 0 && startId > 0 && rule.id() < startId) continue;
      if (targetId > 0) {
        LogicSupport.setDumpLiaFormulas(true);
      }
      final int result = LogicSupport.proveEqByLIAStar2(rule);
      System.out.println("Rule id: " + rule.id() + " is " + LogicSupport.stringifyResult(result));
    }
    // Current statistics:
    final List<Integer> timeOuts = List.of(159, 161, 345);
    final List<Integer> neqs =
        List.of(41, 43, 170);
  }

  @Test
  void statisticsOfCalciteRules() throws IOException {
    final Path res = dataDir().resolve("lia").resolve("calciteOpStatistics_"
        + LocalDateTime.now().format(DateTimeFormatter.ofPattern("MMddHHmmss"))
        + ".csv");
    if (!Files.exists(res)) {
      Files.createDirectories(res.getParent());
      Files.createFile(res);
    }

    final Path testCasesPath = dataDir().resolve("calcite").resolve("calcite_tests");
    final List<QueryPair> queryPairs = readPairs(Files.readAllLines(testCasesPath), "calcite_test");
    final Map<Integer, String> statistics = new HashMap<>();
    for (QueryPair pair : queryPairs) {
      final String sql0 = pair.sql0, sql1 = pair.sql1;
      final StringBuilder sBuilder = new StringBuilder();
      // sub-query
      if (containsIgnoreCase(sql0, " IN ") || containsIgnoreCase(sql1, " IN "))
        sBuilder.append("insub").append(",");
      if (containsIgnoreCase(sql0, " EXISTS ") || containsIgnoreCase(sql1, " EXISTS "))
        sBuilder.append("exists").append(",");
      // join, dedup: use plan to judge
      if (pair.p0 != null && pair.p1 != null) {
        final PlanContext p0 = pair.p0, p1 = pair.p1;
        final List<Integer> nodeIds0 = IntStream.range(1, pair.p0.maxNodeId() + 1).boxed().toList();
        final List<Integer> nodeIds1 = IntStream.range(1, pair.p1.maxNodeId() + 1).boxed().toList();
        if (IterableSupport.any(nodeIds0,
            i -> p0.kindOf(i) == PlanKind.Join && ((JoinNode) (p0.nodeAt(i))).joinKind() == JoinKind.INNER_JOIN) ||
            IterableSupport.any(nodeIds1,
                i -> p1.kindOf(i) == PlanKind.Join && ((JoinNode) (p1.nodeAt(i))).joinKind() == JoinKind.INNER_JOIN)) {
          sBuilder.append("innerjoin").append(",");
        }
        if (IterableSupport.any(nodeIds0,
            i -> p0.kindOf(i) == PlanKind.Join && ((JoinNode) (p0.nodeAt(i))).joinKind() == JoinKind.CROSS_JOIN) ||
            IterableSupport.any(nodeIds1,
                i -> p1.kindOf(i) == PlanKind.Join && ((JoinNode) (p1.nodeAt(i))).joinKind() == JoinKind.CROSS_JOIN)) {
          sBuilder.append("crossjoin").append(",");
        }
        if (IterableSupport.any(nodeIds0,
            i -> p0.kindOf(i) == PlanKind.Join && ((JoinNode) (p0.nodeAt(i))).joinKind().isOuter()) ||
            IterableSupport.any(nodeIds1,
                i -> p1.kindOf(i) == PlanKind.Join && ((JoinNode) (p1.nodeAt(i))).joinKind().isOuter())) {
          sBuilder.append("outerjoin").append(",");
        }
        if (IterableSupport.any(nodeIds0,
            i -> p0.kindOf(i) == PlanKind.Proj && ((ProjNode) (p0.nodeAt(i))).deduplicated()) ||
            IterableSupport.any(nodeIds1,
                i -> p1.kindOf(i) == PlanKind.Proj && ((ProjNode) (p1.nodeAt(i))).deduplicated())) {
          sBuilder.append("dedup").append(",");
        }
      }
      // Or, not, and
      if (containsIgnoreCase(sql0, " OR ") || containsIgnoreCase(sql1, " OR "))
        sBuilder.append("or").append(",");
      if (containsIgnoreCase(sql0, " NOT ") || containsIgnoreCase(sql1, " NOT "))
        sBuilder.append("not").append(",");
      if (pair.pairId() != 69 && (containsIgnoreCase(sql0, " AND ") || containsIgnoreCase(sql1, " AND ")))
        sBuilder.append("and").append(",");
      // set ops
      if ((containsIgnoreCase(sql0, " UNION ") || containsIgnoreCase(sql1, " UNION "))) {
        sBuilder.append("union").append(",");
      }
      if ((containsIgnoreCase(sql0, " INTERSECT ") || containsIgnoreCase(sql1, " INTERSECT "))) {
        sBuilder.append("intersect").append(",");
      }
      if ((containsIgnoreCase(sql0, " EXCEPT ") || containsIgnoreCase(sql1, " EXCEPT "))) {
        sBuilder.append("except").append(",");
      }
      // if ((containsIgnoreCase(sql0, " INTERSECT ") && !containsIgnoreCase(sql0, " INTERSECT ALL ")) ||
      //   (containsIgnoreCase(sql1, " INTERSECT ") && !containsIgnoreCase(sql1, " INTERSECT ALL ")))
      //   sBuilder.append("intersect").append(",");
      // if (containsIgnoreCase(sql0, " INTERSECT ALL") || containsIgnoreCase(sql1, " INTERSECT ALL"))
      //   sBuilder.append("intersect all").append(",");
      // if ((containsIgnoreCase(sql0, " EXCEPT ") && !containsIgnoreCase(sql0, " EXCEPT ALL ")) ||
      //     (containsIgnoreCase(sql1, " EXCEPT ") && !containsIgnoreCase(sql1, " EXCEPT ALL ")))
      //   sBuilder.append("except").append(",");
      // if (containsIgnoreCase(sql0, " EXCEPT ALL") || containsIgnoreCase(sql1, " EXCEPT ALL"))
      //   sBuilder.append("except all").append(",");
      // VALUES
      if (containsIgnoreCase(sql0, "VALUES") || containsIgnoreCase(sql1, "VALUES"))
        sBuilder.append("VALUES").append(",");
      // case when
      if (containsIgnoreCase(sql0, "CASE WHEN") || containsIgnoreCase(sql1, "CASE WHEN"))
        sBuilder.append("case when").append(",");
      // agg funcs
      if (containsIgnoreCase(sql0, "MAX(") || containsIgnoreCase(sql1, "MAX("))
        sBuilder.append("agg_max").append(",");
      if (containsIgnoreCase(sql0, "MIN(") || containsIgnoreCase(sql1, "MIN("))
        sBuilder.append("agg_min").append(",");
      if (containsIgnoreCase(sql0, "COUNT(") || containsIgnoreCase(sql1, "COUNT("))
        sBuilder.append("agg_count").append(",");
      if (containsIgnoreCase(sql0, "SUM(") || containsIgnoreCase(sql1, "SUM("))
        sBuilder.append("agg_sum").append(",");
      if (containsIgnoreCase(sql0, "AVG(") || containsIgnoreCase(sql1, "AVG("))
        sBuilder.append("agg_avg").append(",");
      // others....
      if (containsIgnoreCase(sql0, "ORDER BY") || containsIgnoreCase(sql1, "ORDER BY"))
        sBuilder.append("orderby").append(",");
      if (containsIgnoreCase(sql0, "NULL") || containsIgnoreCase(sql1, "NULL"))
        sBuilder.append("null").append(",");

      if (List.of(163, 182, 194, 205, 216, 226).contains(pair.pairId()))
        sBuilder.append("scalar").append(",");

      IOSupport.appendTo(res, out -> out.printf(sBuilder.toString() + "\n"));
      IOSupport.appendTo(res, out -> out.printf(sBuilder.toString() + "\n"));
    }

  }

  private static boolean containsIgnoreCase(String str, String subStr) {
    return str.contains(subStr.toLowerCase()) || str.contains(subStr.toUpperCase());
  }

  @Test
  void testLiaOnSpiderRules() throws IOException {
    String[] appNames = new String[]{
        "spider_car_1",
        "spider_employee_hire_evaluation",
        "spider_tvshow",
        "spider_singer",
        "spider_course_teach", // instructor
        "spider_student_transcripts_tracking", // course
        "spider_wta_1",
        "spider_cre_Doc_Template_Mgt",
        "spider_poker_player",
        "spider_world_1",
        "spider_pets_1",
        "spider_flight_2", // no schema files
        "spider_concert_singer",
        "spider_orchestra",
        "spider_dog_kennels",
        "spider_network_1", // takes
        "spider_voter_1",
        "spider_museum_visit",
        "spider_battle_death"
    };

    Map<String, List<Integer>> sqlExecResults = new HashMap<String, List<Integer>>();
    sqlExecResults.put("spider_concert_singer.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1)));
    sqlExecResults.put("spider_pets_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1)));
    sqlExecResults.put("spider_car_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0)));
    sqlExecResults.put("spider_flight_2.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1)));
    sqlExecResults.put("spider_employee_hire_evaluation.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_cre_Doc_Template_Mgt.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0)));
    sqlExecResults.put("spider_course_teach.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1)));
    sqlExecResults.put("spider_museum_visit.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1)));
    sqlExecResults.put("spider_wta_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1)));
    sqlExecResults.put("spider_battle_death.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1)));
    sqlExecResults.put("spider_student_transcripts_tracking.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0)));
    sqlExecResults.put("spider_tvshow.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1)));
    sqlExecResults.put("spider_poker_player.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_voter_1.expect.txt", new ArrayList<Integer>(Arrays.asList(0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1)));
    sqlExecResults.put("spider_world_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0)));
    sqlExecResults.put("spider_orchestra.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_network_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0)));
    sqlExecResults.put("spider_dog_kennels.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0)));
    sqlExecResults.put("spider_singer.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0)));


    Map<String, List<Integer>> sqlMatchResults = new HashMap<String, List<Integer>>();
    sqlMatchResults.put("spider_concert_singer.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0)));
    sqlMatchResults.put("spider_pets_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1)));
    sqlMatchResults.put("spider_car_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0)));
    sqlMatchResults.put("spider_flight_2.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0)));
    sqlMatchResults.put("spider_employee_hire_evaluation.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1)));
    sqlMatchResults.put("spider_cre_Doc_Template_Mgt.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0)));
    sqlMatchResults.put("spider_course_teach.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1)));
    sqlMatchResults.put("spider_museum_visit.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1)));
    sqlMatchResults.put("spider_wta_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1)));
    sqlMatchResults.put("spider_battle_death.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1)));
    sqlMatchResults.put("spider_student_transcripts_tracking.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0)));
    sqlMatchResults.put("spider_tvshow.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1)));
    sqlMatchResults.put("spider_poker_player.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlMatchResults.put("spider_voter_1.expect.txt", new ArrayList<Integer>(Arrays.asList(0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1)));
    sqlMatchResults.put("spider_world_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0)));
    sqlMatchResults.put("spider_orchestra.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0)));
    sqlMatchResults.put("spider_network_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0)));
    sqlMatchResults.put("spider_dog_kennels.expect.txt", new ArrayList<Integer>(Arrays.asList(0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1)));
    sqlMatchResults.put("spider_singer.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0)));

    String targetApp = null;
    HashMap<String, ArrayList<Integer>> sqlsolverResultMap = new HashMap<>();
    try (FileWriter fileWriter = new FileWriter(dataDir().resolve("unsound.txt").toString())) {
    for (String appName : appNames) {
      System.out.println(appName + " begin");
      if (targetApp != null && !targetApp.equals(appName))
        continue;
      Path testCasesPath = dataDir().resolve("spider").resolve("rules." + appName + ".sql.txt");
      ArrayList<Integer> sqlsolverResult = testLiaOnSpiderRules(testCasesPath, appName);
      sqlsolverResultMap.put(appName, sqlsolverResult);
      System.out.println(appName + "\n" + sqlsolverResult);
      System.out.println(sqlExecResults.get(appName + ".expect.txt"));
        for (int i = 0; i < sqlsolverResult.size(); i++){
          if (sqlsolverResult.get(i) == 1 && sqlExecResults.get(appName + ".expect.txt").get(i) == 0){
            System.out.println("!!!!!!!Unsound!!!!!! At " + (i + 1));
            fileWriter.append(appName).append(" ").append(String.valueOf(i+1)).append("\n");
          }
        }
  //        assertFalse(sqlsolverResult.get(i) == 1 && sqlExecResults.get(appName + ".expect.txt").get(i) == 0);
      }
    }
  }

  @Test
  void testLiaOnTPCCSparkRules() throws IOException {
    Path testCasesPath = dataDir().resolve("prepared").resolve("rules.tpcc.spark.txt");
    int targetId = -1;
    int[] eqCases = new int[]{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19};
    final Set<Integer> timeouts = Set.of();
    testLiaOnRules(testCasesPath, targetId, eqCases, timeouts, "tpcc");
  }

  @Test
  void testLiaOnTPCCCalciteRules() throws IOException {
    Path testCasesPath = dataDir().resolve("prepared").resolve("rules.tpcc.calcite.txt");
    int targetId = -1;
    int[] eqCases = new int[]{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19};
    final Set<Integer> timeouts = Set.of(18);
    testLiaOnRules(testCasesPath, targetId, eqCases, timeouts, "tpcc");
  }

  @Test
  void testLiaOnTPCHSparkRules() throws IOException {
    Path testCasesPath = dataDir().resolve("prepared").resolve("rules.tpch.spark.txt");
    int targetId = -1;
    int[] eqCases = new int[]{1, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 17, 20};
    final Set<Integer> timeouts = Set.of();
    testLiaOnRules(testCasesPath, targetId, eqCases, timeouts, "tpch");
  }

  @Test
  void testLiaOnTPCHCalciteRules() throws IOException {
    Path testCasesPath = dataDir().resolve("prepared").resolve("rules.tpch.calcite.txt");
    int targetId = 5;
    int[] eqCases = new int[]{};
    final Set<Integer> timeouts = Set.of();
    testLiaOnRules(testCasesPath, targetId, eqCases, timeouts, "tpch");
  }

  @Test
  void testLiaOnTPCHSparkCalciteRules() throws IOException {
    Path testCasesPath = dataDir().resolve("prepared").resolve("rules.tpch.spark.calcite.txt");
    int targetId = -1;
    int[] eqCases = new int[]{};
    final Set<Integer> timeouts = Set.of();
    testLiaOnRules(testCasesPath, targetId, eqCases, timeouts, "tpch");
  }

  @Test
  void testLiaOnJobSparkRules() throws IOException {
    Path testCasesPath = dataDir().resolve("prepared").resolve("rules.job.spark.txt");
    int targetId = -1;
    int[] eqCases = new int[]{};
    final Set<Integer> timeouts = Set.of();
    testLiaOnRules(testCasesPath, targetId, eqCases, timeouts, "job");
  }

  @Test
  void testLiaOnJobCalciteRules() throws IOException {
    Path testCasesPath = dataDir().resolve("prepared").resolve("rules.job.calcite.txt");
    int targetId = -1;
    int[] eqCases = new int[]{};
    final Set<Integer> timeouts = Set.of();
    testLiaOnRules(testCasesPath, targetId, eqCases, timeouts, "job");
  }

  @Test
  void testLiaOnCalciteRules() throws IOException {
    Path testCasesPath = dataDir().resolve("calcite").resolve("calcite_tests");
    int targetId = -1;
    int[] eqCases = new int[]{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232};
    final Set<Integer> timeouts = Set.of();
    testLiaOnRules(testCasesPath, targetId, eqCases, timeouts, "calcite_test");
  }

  @Test
  void testLiaOnSparkRules() throws IOException {
    Path testCasesPath = dataDir().resolve("db_rule_instances").resolve("spark_tests");
    int targetId = -1;
    int[] eqCases = new int[]{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 52, 56, 57, 58, 59, 60, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 124, 125, 126};
    final Set<Integer> timeouts = Set.of();
    testLiaOnRules(testCasesPath, targetId, eqCases, timeouts, "calcite_test");
  }

  ArrayList<Integer> testLiaOnSpiderRules(Path testCasesPath, String appName) throws IOException {
    ArrayList<Integer> sqlsolverResults = new ArrayList<>();
    final List<QueryPair> queryPairs = readPairs(Files.readAllLines(testCasesPath), appName);
    for (QueryPair pair : queryPairs) {
      SqlSolver.initialize();
      QueryUExprICRewriter.selectIC(-1);

      if (pair.p0 == null || pair.p1 == null) {
        System.out.println("Rule id " + pair.pairId() + " is: UNKNOWN");
        sqlsolverResults.add(0);
        continue;
      }
      if (isLiteralEq(pair.p0, pair.p1)) {
        System.out.println("Rule id " + pair.pairId() + " is: EQ");
        sqlsolverResults.add(1);
        continue;
      }

      final String res1 = getCalciteVerifyResultConcrete(pair, false);
      System.out.println("Rule id " + pair.pairId() + " is: " + res1);
      if (res1.equals("EQ")) {
        sqlsolverResults.add(1);
        continue;
      }
      sqlsolverResults.add(0);
    }

    return sqlsolverResults;
  }


  void testLiaOnRules(Path testCasesPath, int targetId, int[] eqCases, Set<Integer> timeouts, String appName) throws IOException {
    final List<QueryPair> queryPairs = readPairs(Files.readAllLines(testCasesPath), appName);
    final int startId = -1;
    final Map<String, List<Integer>> statistics = new HashMap<>();
    boolean verbose = targetId > 0;
    final int ruleCounts = queryPairs.size();
    if (targetId > 0) LogicSupport.setDumpLiaFormulas(true);
    for (QueryPair pair : queryPairs) {
      if (targetId > 0 && pair.pairId() != targetId) continue;
      if (targetId < 0 && startId > 0 && pair.pairId() < startId) continue;
      if (timeouts.contains(pair.pairId())) continue;

      SqlSolver.initialize();
      QueryUExprICRewriter.selectIC(-1);

      if (verbose) System.out.println(pair.sql0 + "\n" + pair.sql1);
      if (verbose) System.out.println(pair.p0 + "\n" + pair.p1);
      // Some special cases: VALUES
      if (pair.p0 == null || pair.p1 == null) {
        if (pair.sql0.contains("VALUES") || pair.sql1.contains("VALUES")) {
          final String result = getCalciteVerifyResultConcrete(pair, verbose);
          System.out.println("Rule id " + pair.pairId() + " is: " + result);
          statistics.computeIfAbsent(result, k -> new ArrayList<>()).add(pair.pairId());
        } else {
          // cannot process other cases currently
          statistics.computeIfAbsent("Cannot parse plan", k -> new ArrayList<>()).add(pair.pairId());
        }
        continue;
      }
      if (isLiteralEq(pair.p0, pair.p1)) {
        System.out.println("Rule id " + pair.pairId() + " is: EQ");
        statistics.computeIfAbsent("EQ", k -> new ArrayList<>()).add(pair.pairId());
        continue;
      }

      final String res1 = getCalciteVerifyResultConcrete(pair, verbose);
      if (res1.equals("EQ")) {
        System.out.println("Rule id " + pair.pairId() + " is: EQ");
        statistics.computeIfAbsent("EQ", k -> new ArrayList<>()).add(pair.pairId());
        continue;
      }
      final String res0 = getCalciteVerifyResultSymbolic(pair, false);
      if (res0.equals("EQ")) {
        System.out.println("Rule id " + pair.pairId() + " is: EQ");
        statistics.computeIfAbsent("EQ", k -> new ArrayList<>()).add(pair.pairId());
        continue;
      }
      System.out.println("Rule id " + pair.pairId() + " is: NEQ");
      statistics.computeIfAbsent("NEQ", k -> new ArrayList<>()).add(pair.pairId());
    }

    for (Map.Entry<String, List<Integer>> entry : statistics.entrySet()) {
      System.out.println(entry.getKey() + ": " + entry.getValue().size());
      System.out.println(entry.getValue() + "\n");
      if (entry.getKey().equals("EQ") && targetId < 0) {
        List<Integer> curEqCases = entry.getValue();
        for (int v : eqCases) {
          if (!curEqCases.contains(v)) {
            System.out.println("warning: case " + v + " becomes NEQ!\n");
          }
        }
        for (int v1 : curEqCases) {
          boolean find = false;
          for(int v2 : eqCases) {
            if (v1==v2) {
              find = true;
              break;
            }
          }
          if(!find) {
            System.out.println("Great: case " + v1 + " becomes EQ!\n");
          }
        }
      }
    }
  }

  @Test
  void testLiaOnCalciteRulesWithVALUES() throws IOException {
    final Path testCasesPath = dataDir().resolve("calcite").resolve("calcite_tests");
    final List<QueryPair> queryPairs = readPairs(Files.readAllLines(testCasesPath), "calcite_test");
    final int targetId = -1, startId = -1;
    final Map<String, List<Integer>> statistics = new HashMap<>();
    final boolean verbose = targetId > 0;
    final List<Integer> valuesSqlList =
        List.of(3, 4, 12, 14, 17, 18, 21, 22, 32, 54, 55, 58, 78, 79, 81, 92, 95, 106, 119, 122, 132, 138, 147, 155, 158, 174, 200, 217, 227);
    for (QueryPair pair : queryPairs) {
      if (targetId > 0 && pair.pairId() != targetId) continue;
      if (targetId < 0 && startId > 0 && pair.pairId() < startId) continue;
      if (!valuesSqlList.contains(pair.pairId())) continue;

      if (verbose) System.out.println(pair.sql0 + "\n" + pair.sql1);
      // Some special cases: VALUES
      if (pair.sql0.contains("VALUES") || pair.sql1.contains("VALUES")) {
        final String result = getCalciteVerifyResultConcrete(pair, verbose);
        System.out.println("Rule id " + pair.pairId() + " is: " + result);
        statistics.computeIfAbsent(result, k -> new ArrayList<>()).add(pair.pairId());
      } else {
        // cannot process other cases currently
        statistics.computeIfAbsent("Cannot parse plan", k -> new ArrayList<>()).add(pair.pairId());
      }
    }

    for (Map.Entry<String, List<Integer>> entry : statistics.entrySet()) {
      System.out.println(entry.getKey() + ": " + entry.getValue().size());
      System.out.println(entry.getValue() + "\n");
    }
  }

  @Test
  void testLiaOnCraftRules() throws IOException {
    final Path ruleFilePath = dataDir().resolve("prepared").resolve("rules.test.txt");
    final SubstitutionBank rules = SubstitutionSupport.loadBank(ruleFilePath);
    int targetId = -1;
    int startId = -1;
    for (Substitution rule : rules.rules()) {
      rule.toString();
      if (targetId > 0 && rule.id() != targetId) continue;
      if (targetId < 0 && startId > 0 && rule.id() < startId) continue;
      final UExprTranslationResult uExprs =
          UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
      if (targetId > 0) {
        System.out.println("Rewritten UExpressions: ");
        System.out.println("[[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
        System.out.println("[[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
        LogicSupport.setDumpLiaFormulas(true);
      }
      final int result = LogicSupport.proveEqByLIAStar(rule);
      System.out.println("Rule id: " + rule.id() + " is " + LogicSupport.stringifyResult(result));
    }
  }

  private String getCalciteVerifyResultSymbolic(QueryPair pair, boolean verbose) {
    int res0, res1;
    verbose = true;
    try {
      res0 = LogicSupport.proveEqByLIAStarSymbolic(pair.p0, pair.p1);
    } catch (Exception | Error exception) {
      if (verbose) exception.printStackTrace();
      res0 = UNKNOWN;
    }
    if (res0 == EQ) return LogicSupport.stringifyResult(res0);
    try {
      res1 = LogicSupport.proveEqByLIAStarSymbolic(pair.p1, pair.p0);
    } catch (Exception | Error exception) {
      if (verbose) exception.printStackTrace();
      res1 = UNKNOWN;
    }
    return res1 == EQ ? "EQ" : "NEQ"; //LogicSupport.stringifyResult(EQ) : LogicSupport.stringifyResult(NEQ);
  }

  private String getCalciteVerifyResultConcrete(QueryPair pair, boolean verbose) {
    try {
      if (pair.sql0.contains("VALUES") || pair.sql1.contains("VALUES")) {
        final UExprConcreteTranslationResult uExprs
            = UExprSupport.translateQueryWithVALUESToUExpr(pair.sql0, pair.sql1, pair.schema, 0);
        if (uExprs == null) {
          return LogicSupport.stringifyResult(NEQ);
        }
        final int result = LogicSupport.proveEqByLIAStar(uExprs);
        return LogicSupport.stringifyResult(result);
      }
      final int result = LogicSupport.proveEqByLIAStarConcrete(pair.p0, pair.p1);
      return LogicSupport.stringifyResult(result);
    } catch (Exception exception) {
      if (verbose) exception.printStackTrace();
      return "exception";
    } catch (Error error) {
      if (verbose) error.printStackTrace();
      return "error";
    }
  }

  private List<QueryPair> readPairs(List<String> lines, String appName) {
    final App app = App.of(appName);
    final Schema schema = app.schema("base");
    CastHandler.setSchema(schema);
    CASTSupport.setSchema(schema);
    SqlSupport.muteParsingError();

    final List<QueryPair> pairs = new ArrayList<>(lines.size() >> 1);
    for (int i = 0, bound = lines.size(); i < bound; i += 2) {
      String sql0 = lines.get(i), sql1 = lines.get(i + 1);
      sql0 = parsePreprocess(sql0);
      sql1 = parsePreprocess(sql1);
      String[] pair = parseCoPreprocess(sql0, sql1);
      sql0 = pair[0];
      sql1 = pair[1];
      final SqlNode q0 = parseSql(MySQL, sql0);
      final SqlNode q1 = parseSql(MySQL, sql1);

      if (q0 == null) {
        final int ruleId = (i + 1) + 1 >> 1;
        System.err.printf("Rule id: %d has unsupported query at line %d \n", ruleId, i + 1);
        System.err.println(getLastError());
        pairs.add(new QueryPair(i + 1, schema, sql0, sql1));
        continue;
      }
      if (q1 == null) {
        final int ruleId = (i + 1) + 1 >> 1;
        System.err.printf("Rule id: %d has unsupported query at line %d \n", ruleId, i + 2);
        System.err.println(getLastError());
        pairs.add(new QueryPair(i + 1, schema, sql0, sql1));
        continue;
      }

      q0.context().setSchema(schema);
      q1.context().setSchema(schema);

      try {
          NormalizationSupport.normalizeAst(q0);
          NormalizationSupport.normalizeAst(q1);
      }catch (Exception e){
        final int ruleId = (i + 1) + 1 >> 1;
        System.err.printf("Rule id: %d has unsupported query at line %d \n", ruleId, i + 2);
        pairs.add(new QueryPair(i + 1, schema, sql0, sql1));
        continue;
      }


      final int checkRuleId = (i + 1) + 1 >> 1;
      final PlanContext p0 = assemblePlan(q0, schema);
      if (p0 == null) {
        final int ruleId = (i + 1) + 1 >> 1;
        System.err.printf("Rule id: %d has wrong query at line %d \n", ruleId, i + 1);
        System.err.println(getLastError());
        pairs.add(new QueryPair(i + 1, schema, sql0, sql1, q0, q1));
        continue;
      }


      final PlanContext p1 = assemblePlan(q1, schema);
      if (p1 == null) {
        final int ruleId = (i + 1) + 1 >> 1;
        System.err.printf("Rule id: %d has wrong query at line %d \n", ruleId, i + 2);
        System.err.println(getLastError());
        pairs.add(new QueryPair(i + 1, schema, sql0, sql1, q0, q1));
        continue;
      }

      pairs.add(new QueryPair(i + 1, schema, sql0, sql1, q0, q1, p0, p1));
    }

    return pairs;
  }

  private static class QueryPair {
    private final int lineNum;
    private final Schema schema;
    private final String sql0, sql1;
    private final SqlNode q0, q1;
    private final PlanContext p0, p1;

    private QueryPair(int lineNum, Schema schema, String sql0, String sql1) {
      this(lineNum, schema, sql0, sql1, null, null, null, null);
    }

    private QueryPair(int lineNum, Schema schema, String sql0, String sql1, SqlNode q0, SqlNode q1) {
      this(lineNum, schema, sql0, sql1, q0, q1, null, null);
    }

    private QueryPair(
        int lineNum,
        Schema schema,
        String sql0, String sql1,
        SqlNode q0, SqlNode q1,
        PlanContext p0, PlanContext p1) {
      this.lineNum = lineNum;
      this.schema = schema;
      this.sql0 = sql0;
      this.sql1 = sql1;
      this.q0 = q0;
      this.q1 = q1;
      this.p0 = p0;
      this.p1 = p1;
    }

    private int pairId() {
      return lineNum + 1 >> 1;
    }
  }
}

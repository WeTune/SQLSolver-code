package wtune.superopt.lia;

import org.junit.jupiter.api.Test;
import wtune.common.utils.IOSupport;
import wtune.common.utils.IterableSupport;
import wtune.sql.SqlSupport;
import wtune.sql.ast.SqlNode;
import wtune.sql.ast.constants.JoinKind;
import wtune.sql.plan.*;
import wtune.sql.plan.normalize.PlanNormalization;
import wtune.sql.preprocess.SqlNodePreprocess;
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
import wtune.superopt.uexpr.UExprSupport;
import wtune.superopt.uexpr.UExprTranslationResult;
import wtune.superopt.uexpr.normalizer.QueryUExprICRewriter;

import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.*;
import java.util.concurrent.*;
import java.util.stream.Collectors;
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
            "spider_battle_death",
            "spider_real_estate_properties"
    };

    Map<String, List<Integer>> sqlExecResults = new HashMap<String, List<Integer>>();
    for (String appName : appNames) {
      Path expectPath = dataDir().resolve("spider/expect").resolve(appName + ".expect.txt");
      sqlExecResults.put( appName + ".expect.txt", Files.readAllLines(expectPath).stream().map(Integer::parseInt).collect(Collectors.toList()));
    }

    Map<String, List<Integer>> expectExceptionCases = new HashMap<String, List<Integer>>();
    Map<String, List<Integer>> finalExceptionCases = new HashMap<String, List<Integer>>();
    Path expectExceptionPath = dataDir().resolve("spider").resolve("expect_error.txt");
    List<String> expectExceptions = Files.readAllLines(expectExceptionPath);
    for (String expectException : expectExceptions) {
      String[] parts = expectException.split("\\s+");
      String appName = parts[0];
      for(int i = 1; i < parts.length;i++) {
        expectExceptionCases.computeIfAbsent(appName, k -> new ArrayList<>()).add(Integer.valueOf(parts[i]));
      }
    }

    String targetApp = null;
    HashMap<String, ArrayList<Integer>> sqlsolverResultMap = new HashMap<>();
    try (FileWriter fileWriter1 = new FileWriter(dataDir().resolve("error.txt").toString())) {
      try (FileWriter fileWriter = new FileWriter(dataDir().resolve("unsound.txt").toString())) {
        for (String appName : appNames) {
          System.out.println(appName + " begin");
          if (targetApp != null && !targetApp.equals(appName))
            continue;
          Path testCasesPath = dataDir().resolve("spider/cases").resolve("rules." + appName + ".sql.txt");
          final List<QueryPair> queryPairs = readPairs(Files.readAllLines(testCasesPath), appName);
          ArrayList<Integer> sqlsolverResult = testLiaOnSpiderRules(queryPairs);
          sqlsolverResultMap.put(appName, sqlsolverResult);
          System.out.println(appName + "\n" + sqlsolverResult);
          System.out.println(sqlExecResults.get(appName + ".expect.txt"));
          for (int i = 0; i < sqlsolverResult.size(); i++) {
            if (!sqlsolverResult.get(i).equals(sqlExecResults.get(appName + ".expect.txt").get(i)) && sqlsolverResult.get(i) >= 0) {
              System.out.println("mismatch at " + (i + 1));
              fileWriter.append(appName).append("\t").append(String.valueOf(i + 1)).append("\t").append(queryPairs.get(i).originSql0).append("\t").append(queryPairs.get(i).originSql1).append("\t")
                      .append(String.valueOf(sqlExecResults.get(appName + ".expect.txt").get(i))).append("\t")
                      .append(String.valueOf(sqlsolverResult.get(i))).append("\n");
            }
            if(sqlsolverResult.get(i) < 0) {
              finalExceptionCases.computeIfAbsent(appName, k -> new ArrayList<>()).add(i+1);
              fileWriter1.append(appName).append("\t").append(String.valueOf(i + 1)).append("\t").append(queryPairs.get(i).originSql0).append("\t").append(queryPairs.get(i).originSql1).append("\t")
                      .append(String.valueOf(sqlExecResults.get(appName + ".expect.txt").get(i))).append("\t")
                      .append(String.valueOf(sqlsolverResult.get(i))).append("\n");
            }
          }
        }
        for(Map.Entry<String, List<Integer>> entry : finalExceptionCases.entrySet()) {
          String key = entry.getKey();
          List<Integer> values = entry.getValue();
          for(Integer value : values) {
            if(!expectExceptionCases.get(key).contains(value)) {
              System.err.println(key + " " + value + " becomes exception unexpectedly!");
            }
          }
        }
      }
    }
  }

  @Test
  void testLiaOnSpiderRulesLarge() throws IOException {
    String[] appNames = new String[]{
            "spider_farm",
            "spider_student_assessment",
            "spider_bike_1",
            "spider_book_2",
            "spider_musical",
            "spider_twitter_1",
            "spider_product_catalog",
            "spider_flight_1",
            "spider_allergy_1",
            "spider_store_1",
            "spider_journal_committee",
            "spider_customers_card_transactions",
            "spider_race_track",
            "spider_coffee_shop",
            "spider_chinook_1",
            "spider_insurance_fnol",
            "spider_medicine_enzyme_interaction",
            "spider_university_basketball",
            "spider_phone_1",
            "spider_match_season",
            "spider_climbing",
            "spider_body_builder",
            "spider_election_representative",
            "spider_apartment_rentals",
            "spider_game_injury",
            "spider_soccer_1",
            "spider_performance_attendance",
            "spider_college_2",
            "spider_debate",
            "spider_insurance_and_eClaims",
            "spider_customers_and_invoices",
            "spider_wedding",
            "spider_theme_gallery",
            "spider_epinions_1",
            "spider_riding_club",
            "spider_gymnast",
            "spider_small_bank_1",
            "spider_browser_web",
            "spider_wrestler",
            "spider_school_finance",
            "spider_protein_institute",
            "spider_cinema",
            "spider_products_for_hire",
            "spider_phone_market",
            "spider_gas_company",
            "spider_party_people",
            "spider_pilot_record",
            "spider_cre_Doc_Control_Systems",
            "spider_company_1",
            "spider_local_govt_in_alabama",
            "spider_formula_1",
            "spider_machine_repair",
            "spider_entrepreneur",
            "spider_perpetrator",
            "spider_csu_1",
            "spider_candidate_poll",
            "spider_movie_1",
            "spider_county_public_safety",
            "spider_inn_1",
            "spider_local_govt_mdm",
            "spider_party_host",
            "spider_storm_record",
            "spider_election",
            "spider_news_report",
            "spider_restaurant_1",
            "spider_customer_deliveries",
            "spider_icfp_1",
            "spider_sakila_1",
            "spider_loan_1",
            "spider_behavior_monitoring",
            "spider_assets_maintenance",
            "spider_station_weather",
            "spider_college_1",
            "spider_sports_competition",
            "spider_manufacturer",
            "spider_hr_1",
            "spider_music_1",
            "spider_baseball_1",
            "spider_mountain_photos",
            "spider_program_share",
            "spider_e_learning",
            "spider_insurance_policies",
            "spider_hospital_1",
            "spider_ship_mission",
            "spider_student_1",
            "spider_company_employee",
            "spider_film_rank",
            "spider_cre_Doc_Tracking_DB",
            "spider_club_1",
            "spider_tracking_grants_for_research",
            "spider_network_2",
            "spider_decoration_competition",
            "spider_document_management",
            "spider_company_office",
            "spider_solvency_ii",
            "spider_entertainment_awards",
            "spider_customers_campaigns_ecommerce",
            "spider_college_3",
            "spider_department_store",
            "spider_aircraft",
            "spider_local_govt_and_lot",
            "spider_school_player",
            "spider_store_product",
            "spider_soccer_2",
            "spider_device",
            "spider_cre_Drama_Workshop_Groups",
            "spider_music_2",
            "spider_manufactory_1",
            "spider_tracking_software_problems",
            "spider_shop_membership",
            "spider_voter_2",
            "spider_products_gen_characteristics",
            "spider_swimming",
            "spider_railway",
            "spider_customers_and_products_contacts",
            "spider_dorm_1",
            "spider_customer_complaints",
            "spider_workshop_paper",
            "spider_tracking_share_transactions",
            "spider_cre_Theme_park",
            "spider_game_1",
            "spider_customers_and_addresses",
            "spider_music_4",
            "spider_roller_coaster",
            "spider_ship_1",
            "spider_city_record",
            "spider_e_government",
            "spider_school_bus",
            "spider_flight_company",
            "spider_cre_Docs_and_Epenses",
            "spider_scientist_1",
            "spider_wine_1",
            "spider_train_station",
            "spider_driving_school",
            "spider_activity_1",
            "spider_flight_4",
            "spider_tracking_orders",
            "spider_architecture",
            "spider_culture_company",
    };

    Map<String, List<Integer>> sqlExecResults = new HashMap<String, List<Integer>>();
    sqlExecResults.put("spider_department_management.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_farm.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_student_assessment.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1)));
    sqlExecResults.put("spider_bike_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0)));
    sqlExecResults.put("spider_book_2.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_musical.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_twitter_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_product_catalog.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_flight_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1)));
    sqlExecResults.put("spider_allergy_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_store_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_journal_committee.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_customers_card_transactions.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_race_track.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_coffee_shop.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_chinook_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_insurance_fnol.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_medicine_enzyme_interaction.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_university_basketball.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_phone_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_match_season.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_climbing.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_body_builder.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_election_representative.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_apartment_rentals.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_game_injury.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_soccer_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_performance_attendance.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_college_2.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_debate.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1)));
    sqlExecResults.put("spider_insurance_and_eClaims.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_customers_and_invoices.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1)));
    sqlExecResults.put("spider_wedding.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_theme_gallery.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_epinions_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_riding_club.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_gymnast.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_small_bank_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1)));
    sqlExecResults.put("spider_browser_web.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_wrestler.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_school_finance.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1)));
    sqlExecResults.put("spider_protein_institute.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_cinema.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_products_for_hire.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_phone_market.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_gas_company.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1)));
    sqlExecResults.put("spider_party_people.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_pilot_record.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_cre_Doc_Control_Systems.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_company_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_local_govt_in_alabama.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_formula_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1)));
    sqlExecResults.put("spider_machine_repair.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_entrepreneur.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_perpetrator.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_csu_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_candidate_poll.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_movie_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_county_public_safety.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_inn_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_local_govt_mdm.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1)));
    sqlExecResults.put("spider_party_host.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_storm_record.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_election.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_news_report.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_restaurant_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_customer_deliveries.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1)));
    sqlExecResults.put("spider_icfp_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_sakila_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_loan_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_behavior_monitoring.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0)));
    sqlExecResults.put("spider_assets_maintenance.expect.txt", new ArrayList<Integer>(Arrays.asList(0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1)));
    sqlExecResults.put("spider_station_weather.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_college_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_sports_competition.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_manufacturer.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_hr_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1)));
    sqlExecResults.put("spider_music_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_baseball_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_mountain_photos.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_program_share.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_e_learning.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_insurance_policies.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_hospital_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1)));
    sqlExecResults.put("spider_ship_mission.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_student_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1)));
    sqlExecResults.put("spider_company_employee.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1)));
    sqlExecResults.put("spider_film_rank.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_cre_Doc_Tracking_DB.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0)));
    sqlExecResults.put("spider_club_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_tracking_grants_for_research.expect.txt", new ArrayList<Integer>(Arrays.asList(0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1)));
    sqlExecResults.put("spider_network_2.expect.txt", new ArrayList<Integer>(Arrays.asList(0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1)));
    sqlExecResults.put("spider_decoration_competition.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_document_management.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_company_office.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_solvency_ii.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_entertainment_awards.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_customers_campaigns_ecommerce.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_college_3.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_department_store.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1)));
    sqlExecResults.put("spider_aircraft.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_local_govt_and_lot.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_school_player.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_store_product.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1)));
    sqlExecResults.put("spider_soccer_2.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_device.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_cre_Drama_Workshop_Groups.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0)));
    sqlExecResults.put("spider_music_2.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_manufactory_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_tracking_software_problems.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_shop_membership.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_voter_2.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_products_gen_characteristics.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_swimming.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_railway.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_customers_and_products_contacts.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_dorm_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1)));
    sqlExecResults.put("spider_customer_complaints.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_workshop_paper.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_tracking_share_transactions.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1)));
    sqlExecResults.put("spider_cre_Theme_park.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_game_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_customers_and_addresses.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_music_4.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_roller_coaster.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_ship_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_city_record.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_e_government.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_school_bus.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_flight_company.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_cre_Docs_and_Epenses.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0)));
    sqlExecResults.put("spider_scientist_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_wine_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_train_station.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_driving_school.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_activity_1.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0)));
    sqlExecResults.put("spider_flight_4.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0)));
    sqlExecResults.put("spider_tracking_orders.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1)));
    sqlExecResults.put("spider_architecture.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1)));
    sqlExecResults.put("spider_culture_company.expect.txt", new ArrayList<Integer>(Arrays.asList(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)));

    String targetApp = null;
    HashMap<String, ArrayList<Integer>> sqlsolverResultMap = new HashMap<>();
    try (FileWriter fileWriter = new FileWriter(dataDir().resolve("unsound.txt").toString())) {
      for (String appName : appNames) {
        System.out.println(appName + " begin");
        if (targetApp != null && !targetApp.equals(appName))
          continue;
        Path testCasesPath = dataDir().resolve("spider_large").resolve("rules." + appName + ".sql.txt");
        ArrayList<Integer> sqlsolverResult = null;
        final List<QueryPair> queryPairs = readPairs(Files.readAllLines(testCasesPath), appName);
        sqlsolverResult = testLiaOnSpiderRules(queryPairs);
        sqlsolverResultMap.put(appName, sqlsolverResult);
        System.out.println(appName + "\n" + sqlsolverResult);
        System.out.println(sqlExecResults.get(appName + ".expect.txt"));
        for (int i = 0; i < sqlsolverResult.size(); i++){
          if (!sqlsolverResult.get(i).equals(sqlExecResults.get(appName + ".expect.txt").get(i)) && sqlsolverResult.get(i) >= 0){
            System.out.println("mismatch at " + (i + 1));
            fileWriter.append(appName).append("\t").append(String.valueOf(i+1)).append("\t").append(queryPairs.get(i).sql0).append("\t").append(queryPairs.get(i).sql1).append("\t")
                    .append(String.valueOf(sqlExecResults.get(appName + ".expect.txt").get(i))).append("\t")
                    .append(String.valueOf(sqlsolverResult.get(i))).append("\n");
          }
        }
      }
    }
  }

  @Test
  void testLiaOnSpiderRulesRESDSQLTestSet() throws IOException {
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
            "spider_battle_death",
            "spider_real_estate_properties"
    };

    Map<String, List<Integer>> sqlExecResults = new HashMap<String, List<Integer>>();
    for (String appName : appNames) {
      Path expectPath = dataDir().resolve("spider_RESDSQL_test_set/expect").resolve(appName + ".expect.txt");
      sqlExecResults.put( appName + ".expect.txt", Files.readAllLines(expectPath).stream().map(Integer::parseInt).collect(Collectors.toList()));
    }

    Map<String, List<Integer>> expectExceptionCases = new HashMap<String, List<Integer>>();
    Map<String, List<Integer>> finalExceptionCases = new HashMap<String, List<Integer>>();
    Path expectExceptionPath = dataDir().resolve("spider_RESDSQL_test_set").resolve("expect_error.txt");
    List<String> expectExceptions = Files.readAllLines(expectExceptionPath);
    for (String expectException : expectExceptions) {
      String[] parts = expectException.split("\\s+");
      String appName = parts[0];
      for(int i = 1; i < parts.length;i++) {
        expectExceptionCases.computeIfAbsent(appName, k -> new ArrayList<>()).add(Integer.valueOf(parts[i]));
      }
    }

    String targetApp = null;
    HashMap<String, ArrayList<Integer>> sqlsolverResultMap = new HashMap<>();
    try (FileWriter fileWriter1 = new FileWriter(dataDir().resolve("error.txt").toString())) {
      try (FileWriter fileWriter = new FileWriter(dataDir().resolve("unsound.txt").toString())) {
        for (String appName : appNames) {
          System.out.println(appName + " begin");
          if (targetApp != null && !targetApp.equals(appName))
            continue;
          Path testCasesPath = dataDir().resolve("spider_RESDSQL_test_set/cases").resolve("rules." + appName + ".sql.txt");
          final List<QueryPair> queryPairs = readPairs(Files.readAllLines(testCasesPath), appName);
          ArrayList<Integer> sqlsolverResult = testLiaOnSpiderRules(queryPairs);
          sqlsolverResultMap.put(appName, sqlsolverResult);
          System.out.println(appName + "\n" + sqlsolverResult);
          System.out.println(sqlExecResults.get(appName + ".expect.txt"));
          for (int i = 0; i < sqlsolverResult.size(); i++) {
            if (!sqlsolverResult.get(i).equals(sqlExecResults.get(appName + ".expect.txt").get(i)) && sqlsolverResult.get(i) >= 0) {
              System.out.println("mismatch at " + (i + 1));
              fileWriter.append(appName).append("\t").append(String.valueOf(i + 1)).append("\t").append(queryPairs.get(i).sql0).append("\t").append(queryPairs.get(i).sql1).append("\t")
                      .append(String.valueOf(sqlExecResults.get(appName + ".expect.txt").get(i))).append("\t")
                      .append(String.valueOf(sqlsolverResult.get(i))).append("\n");
            }
            if(sqlsolverResult.get(i) < 0) {
              finalExceptionCases.computeIfAbsent(appName, k -> new ArrayList<>()).add(i+1);
              fileWriter1.append(appName).append("\t").append(String.valueOf(i + 1)).append("\t").append(queryPairs.get(i).sql0).append("\t").append(queryPairs.get(i).sql1).append("\t")
                      .append(String.valueOf(sqlsolverResult.get(i))).append("\n");
            }
          }
        }
        for(Map.Entry<String, List<Integer>> entry : finalExceptionCases.entrySet()) {
          String key = entry.getKey();
          List<Integer> values = entry.getValue();
          for(Integer value : values) {
            if(!expectExceptionCases.get(key).contains(value)) {
              System.err.println(key + " " + value + " becomes exception unexpectedly!");
            }
          }
        }
      }
    }
  }

  @Test
  void testLiaOnSpiderRulesC3SQLTestSet() throws IOException {
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
            "spider_battle_death",
            "spider_real_estate_properties"
    };

    Map<String, List<Integer>> sqlExecResults = new HashMap<String, List<Integer>>();
    for (String appName : appNames) {
      Path expectPath = dataDir().resolve("spider_C3SQL_test_set/expect").resolve(appName + ".expect.txt");
      sqlExecResults.put( appName + ".expect.txt", Files.readAllLines(expectPath).stream().map(Integer::parseInt).collect(Collectors.toList()));
    }

    Map<String, List<Integer>> expectExceptionCases = new HashMap<String, List<Integer>>();
    Map<String, List<Integer>> finalExceptionCases = new HashMap<String, List<Integer>>();
    Path expectExceptionPath = dataDir().resolve("spider_C3SQL_test_set").resolve("expect_error.txt");
    List<String> expectExceptions = Files.readAllLines(expectExceptionPath);
    for (String expectException : expectExceptions) {
      String[] parts = expectException.split("\\s+");
      String appName = parts[0];
      for(int i = 1; i < parts.length;i++) {
        expectExceptionCases.computeIfAbsent(appName, k -> new ArrayList<>()).add(Integer.valueOf(parts[i]));
      }
    }

    String targetApp = null;
    HashMap<String, ArrayList<Integer>> sqlsolverResultMap = new HashMap<>();
    try (FileWriter fileWriter1 = new FileWriter(dataDir().resolve("error.txt").toString())) {
      try (FileWriter fileWriter = new FileWriter(dataDir().resolve("unsound.txt").toString())) {
        for (String appName : appNames) {
          System.out.println(appName + " begin");
          if (targetApp != null && !targetApp.equals(appName))
            continue;
          Path testCasesPath = dataDir().resolve("spider_C3SQL_test_set/cases").resolve("rules." + appName + ".sql.txt");
          final List<QueryPair> queryPairs = readPairs(Files.readAllLines(testCasesPath), appName);
          ArrayList<Integer> sqlsolverResult = testLiaOnSpiderRules(queryPairs);
          sqlsolverResultMap.put(appName, sqlsolverResult);
          System.out.println(appName + "\n" + sqlsolverResult);
          System.out.println(sqlExecResults.get(appName + ".expect.txt"));
          for (int i = 0; i < sqlsolverResult.size(); i++) {
            if (!sqlsolverResult.get(i).equals(sqlExecResults.get(appName + ".expect.txt").get(i)) && sqlsolverResult.get(i) >= 0) {
              System.out.println("mismatch at " + (i + 1));
              fileWriter.append(appName).append("\t").append(String.valueOf(i + 1)).append("\t").append(queryPairs.get(i).sql0).append("\t").append(queryPairs.get(i).sql1).append("\t")
                      .append(String.valueOf(sqlExecResults.get(appName + ".expect.txt").get(i))).append("\t")
                      .append(String.valueOf(sqlsolverResult.get(i))).append("\n");
            }
            if(sqlsolverResult.get(i) < 0) {
              finalExceptionCases.computeIfAbsent(appName, k -> new ArrayList<>()).add(i+1);
              fileWriter1.append(appName).append("\t").append(String.valueOf(i + 1)).append("\t").append(queryPairs.get(i).sql0).append("\t").append(queryPairs.get(i).sql1).append("\t")
                      .append(String.valueOf(sqlsolverResult.get(i))).append("\n");
            }
          }
        }
        for(Map.Entry<String, List<Integer>> entry : finalExceptionCases.entrySet()) {
          String key = entry.getKey();
          List<Integer> values = entry.getValue();
          for(Integer value : values) {
            if(!expectExceptionCases.get(key).contains(value)) {
              System.err.println(key + " " + value + " becomes exception unexpectedly!");
            }
          }
        }
      }
    }
  }

  @Test
  void testLiaOnSpiderRulesDAILSQLTestSet() throws IOException {
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
            "spider_battle_death",
            "spider_real_estate_properties"
    };

    Map<String, List<Integer>> sqlExecResults = new HashMap<String, List<Integer>>();
    for (String appName : appNames) {
      Path expectPath = dataDir().resolve("spider_DAIL-SQL_test_set/expect").resolve(appName + ".expect.txt");
      sqlExecResults.put( appName + ".expect.txt", Files.readAllLines(expectPath).stream().map(Integer::parseInt).collect(Collectors.toList()));
    }

    Map<String, List<Integer>> expectExceptionCases = new HashMap<String, List<Integer>>();
    Map<String, List<Integer>> finalExceptionCases = new HashMap<String, List<Integer>>();
    Path expectExceptionPath = dataDir().resolve("spider_DAIL-SQL_test_set").resolve("expect_error.txt");
    List<String> expectExceptions = Files.readAllLines(expectExceptionPath);
    for (String expectException : expectExceptions) {
      String[] parts = expectException.split("\\s+");
      String appName = parts[0];
      for(int i = 1; i < parts.length;i++) {
        expectExceptionCases.computeIfAbsent(appName, k -> new ArrayList<>()).add(Integer.valueOf(parts[i]));
      }
    }

    String targetApp = null;
    HashMap<String, ArrayList<Integer>> sqlsolverResultMap = new HashMap<>();
    try (FileWriter fileWriter1 = new FileWriter(dataDir().resolve("error.txt").toString())) {
      try (FileWriter fileWriter = new FileWriter(dataDir().resolve("unsound.txt").toString())) {
        for (String appName : appNames) {
          System.out.println(appName + " begin");
          if (targetApp != null && !targetApp.equals(appName))
            continue;
          Path testCasesPath = dataDir().resolve("spider_DAIL-SQL_test_set/cases").resolve("rules." + appName + ".sql.txt");
          final List<QueryPair> queryPairs = readPairs(Files.readAllLines(testCasesPath), appName);
          ArrayList<Integer> sqlsolverResult = testLiaOnSpiderRules(queryPairs);
          sqlsolverResultMap.put(appName, sqlsolverResult);
          System.out.println(appName + "\n" + sqlsolverResult);
          System.out.println(sqlExecResults.get(appName + ".expect.txt"));
          for (int i = 0; i < sqlsolverResult.size(); i++) {
            if (!sqlsolverResult.get(i).equals(sqlExecResults.get(appName + ".expect.txt").get(i)) && sqlsolverResult.get(i) >= 0) {
              System.out.println("mismatch at " + (i + 1));
              fileWriter.append(appName).append("\t").append(String.valueOf(i + 1)).append("\t").append(queryPairs.get(i).sql0).append("\t").append(queryPairs.get(i).sql1).append("\t")
                      .append(String.valueOf(sqlExecResults.get(appName + ".expect.txt").get(i))).append("\t")
                      .append(String.valueOf(sqlsolverResult.get(i))).append("\n");
            }
            if(sqlsolverResult.get(i) < 0) {
              finalExceptionCases.computeIfAbsent(appName, k -> new ArrayList<>()).add(i+1);
              fileWriter1.append(appName).append("\t").append(String.valueOf(i + 1)).append("\t").append(queryPairs.get(i).sql0).append("\t").append(queryPairs.get(i).sql1).append("\t")
                      .append(String.valueOf(sqlsolverResult.get(i))).append("\n");
            }
          }
        }
        for(Map.Entry<String, List<Integer>> entry : finalExceptionCases.entrySet()) {
          String key = entry.getKey();
          List<Integer> values = entry.getValue();
          for(Integer value : values) {
            if(!expectExceptionCases.get(key).contains(value)) {
              System.err.println(key + " " + value + " becomes exception unexpectedly!");
            }
          }
        }
      }
    }
  }

  @Test
  void testLiaOnSpiderRulesDAILSQLSelfConsistencyTestSet() throws IOException {
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
            "spider_battle_death",
            "spider_real_estate_properties"
    };

    Map<String, List<Integer>> sqlExecResults = new HashMap<String, List<Integer>>();
    for (String appName : appNames) {
      Path expectPath = dataDir().resolve("spider_DAIL-SQL+self-consistency_test_set/expect").resolve(appName + ".expect.txt");
      sqlExecResults.put( appName + ".expect.txt", Files.readAllLines(expectPath).stream().map(Integer::parseInt).collect(Collectors.toList()));
    }

    Map<String, List<Integer>> expectExceptionCases = new HashMap<String, List<Integer>>();
    Map<String, List<Integer>> finalExceptionCases = new HashMap<String, List<Integer>>();
    Path expectExceptionPath = dataDir().resolve("spider_DAIL-SQL+self-consistency_test_set").resolve("expect_error.txt");
    List<String> expectExceptions = Files.readAllLines(expectExceptionPath);
    for (String expectException : expectExceptions) {
      String[] parts = expectException.split("\\s+");
      String appName = parts[0];
      for(int i = 1; i < parts.length;i++) {
        expectExceptionCases.computeIfAbsent(appName, k -> new ArrayList<>()).add(Integer.valueOf(parts[i]));
      }
    }

    String targetApp = null;
    HashMap<String, ArrayList<Integer>> sqlsolverResultMap = new HashMap<>();
    try (FileWriter fileWriter1 = new FileWriter(dataDir().resolve("error.txt").toString())) {
      try (FileWriter fileWriter = new FileWriter(dataDir().resolve("unsound.txt").toString())) {
        for (String appName : appNames) {
          System.out.println(appName + " begin");
          if (targetApp != null && !targetApp.equals(appName))
            continue;
          Path testCasesPath = dataDir().resolve("spider_DAIL-SQL+self-consistency_test_set/cases").resolve("rules." + appName + ".sql.txt");
          final List<QueryPair> queryPairs = readPairs(Files.readAllLines(testCasesPath), appName);
          ArrayList<Integer> sqlsolverResult = testLiaOnSpiderRules(queryPairs);
          sqlsolverResultMap.put(appName, sqlsolverResult);
          System.out.println(appName + "\n" + sqlsolverResult);
          System.out.println(sqlExecResults.get(appName + ".expect.txt"));
          for (int i = 0; i < sqlsolverResult.size(); i++) {
            if (!sqlsolverResult.get(i).equals(sqlExecResults.get(appName + ".expect.txt").get(i)) && sqlsolverResult.get(i) >= 0) {
              System.out.println("mismatch at " + (i + 1));
              fileWriter.append(appName).append("\t").append(String.valueOf(i + 1)).append("\t").append(queryPairs.get(i).originSql0).append("\t").append(queryPairs.get(i).originSql1).append("\t")
                      .append(String.valueOf(sqlExecResults.get(appName + ".expect.txt").get(i))).append("\t")
                      .append(String.valueOf(sqlsolverResult.get(i))).append("\n");
            }
            if(sqlsolverResult.get(i) < 0) {
              finalExceptionCases.computeIfAbsent(appName, k -> new ArrayList<>()).add(i+1);
              fileWriter1.append(appName).append("\t").append(String.valueOf(i + 1)).append("\t").append(queryPairs.get(i).originSql0).append("\t").append(queryPairs.get(i).originSql1).append("\t")
                      .append(String.valueOf(sqlExecResults.get(appName + ".expect.txt").get(i))).append("\t")
                      .append(String.valueOf(sqlsolverResult.get(i))).append("\n");
            }
          }
        }
        for(Map.Entry<String, List<Integer>> entry : finalExceptionCases.entrySet()) {
          String key = entry.getKey();
          List<Integer> values = entry.getValue();
          for(Integer value : values) {
            if(!expectExceptionCases.get(key).contains(value)) {
              System.err.println(key + " " + value + " becomes exception unexpectedly!");
            }
          }
        }
      }
    }
  }

  @Test
  void testLiaOnTPCCSparkRules() throws IOException {
    Path testCasesPath = dataDir().resolve("prepared").resolve("rules.tpcc.spark.txt");
    int targetId = -1;
    int[] eqCases = new int[]{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19};
    final Set<Integer> timeouts = Set.of();
    testLiaOnRulesConcrete(testCasesPath, targetId, eqCases, timeouts, "tpcc");
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
    int[] eqCases = new int[]{1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 20, 21, 22};
    final Set<Integer> timeouts = Set.of();
    testLiaOnRulesConcrete(testCasesPath, targetId, eqCases, timeouts, "tpch");
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
    long timeout = 1800;
    int[] eqCases = new int[]{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113};
    // timeout cases may become EQ after timeout
    final Set<Integer> timeouts = Set.of();
    testLiaOnRulesConcrete(testCasesPath, targetId, eqCases, timeouts, "job", timeout);
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
    testLiaOnRulesConcrete(testCasesPath, targetId, eqCases, timeouts, "calcite_test");
  }

  @Test
  void testLiaOnSparkRules() throws IOException {
    Path testCasesPath = dataDir().resolve("db_rule_instances").resolve("spark_tests");
    int targetId = -1;
    int[] eqCases = new int[]{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 52, 56, 57, 58, 59, 60, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 124, 125, 126};
    final Set<Integer> timeouts = Set.of();
    testLiaOnRulesConcrete(testCasesPath, targetId, eqCases, timeouts, "calcite_test");
  }

  ArrayList<Integer> testLiaOnSpiderRules(List<QueryPair> queryPairs) throws IOException {
    ArrayList<Integer> sqlsolverResults = new ArrayList<>();

    for (QueryPair pair : queryPairs) {
      SqlSolver.initialize();
      QueryUExprICRewriter.selectIC(-1);

      if (pair.p0 == null || pair.p1 == null) {
        // when it contains wrong sql, it should be NEQ
        System.out.println("Rule id " + pair.pairId() + " is: NEQ");
        sqlsolverResults.add(-2);
        continue;
      }
      if (isSemanticError(pair.p0, pair.p1)) {
        System.out.println("Rule id " + pair.pairId() + " is: EQ");
        sqlsolverResults.add(1);
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
      }else if (res1.equals("NEQ")){
        sqlsolverResults.add(0);
        continue;
      }
      sqlsolverResults.add(-1);
    }

    return sqlsolverResults;
  }

  private boolean verifyConcreteSymbolic(QueryPair pair, boolean verbose, Map<String, List<Integer>> statistics) {
    final String res1 = getCalciteVerifyResultConcrete(pair, verbose);
    if (res1.equals("EQ")) {
      System.out.println("Rule id " + pair.pairId() + " is: EQ");
      statistics.computeIfAbsent("EQ", k -> new ArrayList<>()).add(pair.pairId());
      return true;
    }
    final String res0 = getCalciteVerifyResultSymbolic(pair, false);
    if (res0.equals("EQ")) {
      System.out.println("Rule id " + pair.pairId() + " is: EQ");
      statistics.computeIfAbsent("EQ", k -> new ArrayList<>()).add(pair.pairId());
      return true;
    }
    return false;
  }

  private boolean verifyConcreteSymbolicWithTimeout(QueryPair pair, boolean verbose, Map<String, List<Integer>> statistics, long timeout) {
    if (timeout <= 0) return verifyConcreteSymbolic(pair, verbose, statistics);

    ExecutorService service = Executors.newSingleThreadExecutor();
    Future<Boolean> future = service.submit(() -> verifyConcreteSymbolic(pair, verbose, statistics));
    try {
      return future.get(timeout, TimeUnit.SECONDS);
    } catch (TimeoutException e) {
      System.err.println("Case " + pair.pairId() + " timeout");
      future.cancel(true);
    } catch (Exception e) {
      e.printStackTrace();
    }
    service.shutdownNow();
    return false;
  }

  void testLiaOnRules(Path testCasesPath, int targetId, int[] eqCases, Set<Integer> timeouts, String appName) throws IOException {
    testLiaOnRules(testCasesPath, targetId, eqCases, timeouts, appName, -1);
  }

  void testLiaOnRules(Path testCasesPath, int targetId, int[] eqCases, Set<Integer> timeouts, String appName, long timeout) throws IOException {
    final List<QueryPair> queryPairs = readPairs(Files.readAllLines(testCasesPath), appName);
    final int startId = -1;
    final Map<String, List<Integer>> statistics = new ConcurrentHashMap<>();
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

      if (verifyConcreteSymbolicWithTimeout(pair, verbose, statistics, timeout)) continue;

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

  private boolean verifyConcrete(QueryPair pair, boolean verbose, Map<String, List<Integer>> statistics) {
    final String res1 = getCalciteVerifyResultConcrete(pair, verbose);
    if (res1.equals("EQ")) {
      System.out.println("Rule id " + pair.pairId() + " is: EQ");
      statistics.computeIfAbsent("EQ", k -> new ArrayList<>()).add(pair.pairId());
      return true;
    }
    return false;
  }

  private boolean verifyConcreteWithTimeout(QueryPair pair, boolean verbose, Map<String, List<Integer>> statistics, long timeout) {
    if (timeout <= 0) return verifyConcrete(pair, verbose, statistics);

    ExecutorService service = Executors.newSingleThreadExecutor();
    Future<Boolean> future = service.submit(() -> verifyConcrete(pair, verbose, statistics));
    try {
      return future.get(timeout, TimeUnit.SECONDS);
    } catch (TimeoutException e) {
      System.err.println("Case " + pair.pairId() + " timeout");
    } catch (Exception e) {
      e.printStackTrace();
    }
    return false;
  }

  void testLiaOnRulesConcrete(Path testCasesPath, int targetId, int[] eqCases, Set<Integer> timeouts, String appName) throws IOException {
    testLiaOnRulesConcrete(testCasesPath, targetId, eqCases, timeouts, appName, -1);
  }

  void testLiaOnRulesConcrete(Path testCasesPath, int targetId, int[] eqCases, Set<Integer> timeouts, String appName, long timeout) throws IOException {
    final List<QueryPair> queryPairs = readPairs(Files.readAllLines(testCasesPath), appName);
    final int startId = -1;
    final Map<String, List<Integer>> statistics = new ConcurrentHashMap<>();
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
      if (isSemanticError(pair.p0, pair.p1)) {
        System.out.println("Rule id " + pair.pairId() + " is: EQ");
        statistics.computeIfAbsent("EQ", k -> new ArrayList<>()).add(pair.pairId());
        continue;
      }
      if (isLiteralEq(pair.p0, pair.p1)) {
        System.out.println("Rule id " + pair.pairId() + " is: EQ");
        statistics.computeIfAbsent("EQ", k -> new ArrayList<>()).add(pair.pairId());
        continue;
      }

      if (verifyConcreteWithTimeout(pair, verbose, statistics, timeout)) continue;

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
    } catch (OutOfMemoryError e) {
      System.err.println("out of memory");
      if (verbose) e.printStackTrace();
      return "error";
    } catch (Error error) {
      if (verbose) error.printStackTrace();
      return "error";
    }
  }

  private List<QueryPair> readPairs(List<String> lines, String appName) {
    final App app = App.of(appName);
    final Schema schema = app.schema("base");
    SqlNodePreprocess.setSchema(schema);
    CASTSupport.setSchema(schema);
    SqlSupport.muteParsingError();

    final List<QueryPair> pairs = new ArrayList<>(lines.size() >> 1);
    for (int i = 0, bound = lines.size(); i < bound; i += 2) {
      String sql0 = lines.get(i), sql1 = lines.get(i + 1);
      String originSql0 = sql0.substring(0), originSql1 = sql1.substring(0);
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
        pairs.add(new QueryPair(i + 1, schema, sql0, sql1, originSql0, originSql1));
        continue;
      }
      if (q1 == null) {
        final int ruleId = (i + 1) + 1 >> 1;
        System.err.printf("Rule id: %d has unsupported query at line %d \n", ruleId, i + 2);
        System.err.println(getLastError());
        pairs.add(new QueryPair(i + 1, schema, sql0, sql1, originSql0, originSql1));
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
        pairs.add(new QueryPair(i + 1, schema, sql0, sql1, originSql0, originSql1));
        continue;
      }


      final int checkRuleId = (i + 1) + 1 >> 1;
      final PlanContext p0 = assemblePlan(q0, schema);
      if (p0 == null) {
        final int ruleId = (i + 1) + 1 >> 1;
        System.err.printf("Rule id: %d has wrong query at line %d \n", ruleId, i + 1);
        System.err.println(getLastError());
        pairs.add(new QueryPair(i + 1, schema, sql0, sql1, originSql0, originSql1, q0, q1));
        continue;
      }


      final PlanContext p1 = assemblePlan(q1, schema);
      if (p1 == null) {
        final int ruleId = (i + 1) + 1 >> 1;
        System.err.printf("Rule id: %d has wrong query at line %d \n", ruleId, i + 2);
        System.err.println(getLastError());
        pairs.add(new QueryPair(i + 1, schema, sql0, sql1, originSql0, originSql1, q0, q1));
        continue;
      }

      try {
        PlanNormalization.normalizePlan(p0);
        PlanNormalization.normalizePlan(p1);
      }catch (Exception e){
        final int ruleId = (i + 1) + 1 >> 1;
        System.err.printf("Rule id: %d has unsupported plan normalize operator at line %d \n", ruleId, i + 2);
        pairs.add(new QueryPair(i + 1, schema, sql0, sql1));
        continue;
      }

      pairs.add(new QueryPair(i + 1, schema, sql0, sql1, originSql0, originSql1, q0, q1, p0, p1));
    }

    return pairs;
  }

  private static class QueryPair {
    private final int lineNum;
    private final Schema schema;
    private final String sql0, sql1;

    private final String originSql0, originSql1;
    private final SqlNode q0, q1;
    private final PlanContext p0, p1;

    private QueryPair(int lineNum, Schema schema, String sql0, String sql1) {
      this(lineNum, schema, sql0, sql1, null, null, null, null, null, null);
    }

    private QueryPair(int lineNum, Schema schema, String sql0, String sql1, String originSql0, String originSql1) {
      this(lineNum, schema, sql0, sql1, originSql0, originSql1, null, null, null, null);
    }

    private QueryPair(int lineNum, Schema schema, String sql0, String sql1, SqlNode q0, SqlNode q1) {
      this(lineNum, schema, sql0, sql1, null, null, q0, q1, null, null);
    }

    private QueryPair(int lineNum, Schema schema, String sql0, String sql1, String originSql0, String originSql1, SqlNode q0, SqlNode q1) {
      this(lineNum, schema, sql0, sql1, originSql0, originSql1, q0, q1, null, null);
    }

    private QueryPair(
        int lineNum,
        Schema schema,
        String sql0, String sql1,
        String originSql0, String originSql1,
        SqlNode q0, SqlNode q1,
        PlanContext p0, PlanContext p1) {
      this.lineNum = lineNum;
      this.schema = schema;
      this.sql0 = sql0;
      this.sql1 = sql1;
      this.originSql0 = originSql0;
      this.originSql1 = originSql1;
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

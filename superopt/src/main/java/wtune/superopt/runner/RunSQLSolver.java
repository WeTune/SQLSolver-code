package wtune.superopt.runner;

import wtune.common.utils.Args;
import wtune.sql.SqlSupport;
import wtune.sql.ast.SqlNode;
import wtune.sql.plan.PlanContext;
import wtune.sql.preprocess.SqlNodePreprocess;
import wtune.sql.schema.Schema;
import wtune.sql.support.action.NormalizationSupport;
import wtune.stmt.App;
import wtune.superopt.logic.CASTSupport;
import wtune.superopt.logic.LogicSupport;
import wtune.superopt.logic.SqlSolver;
import wtune.superopt.uexpr.UExprConcreteTranslationResult;
import wtune.superopt.uexpr.UExprSupport;
import wtune.superopt.uexpr.normalizer.QueryUExprICRewriter;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;

import static wtune.common.datasource.DbSupport.MySQL;
import static wtune.sql.SqlSupport.*;
import static wtune.sql.plan.PlanSupport.*;
import static wtune.superopt.logic.LogicSupport.*;

public class RunSQLSolver implements Runner {

  private static final String CALCITE_APP_NAME = "calcite_test";

  private Path out;
  private Path testCases;
  private int targetPairId;
  private List<Integer> skipPairIds;
  private int rounds = 5;
  private boolean time, tsvNeq;
  private App app;

  private Path tsvFilePath, outPath;
  private StringBuilder tsvStrBuilder, outStrBuilder;
  private long thisTime; // last case time

  private void println(String str) {
    System.out.println(str);
    if (outPath != null) outStrBuilder.append(str).append("\n");
  }

  @Override
  public void prepare(String[] argStrings) {
    final Args args = Args.parse(argStrings, 1);
    time = args.getOptional("time", boolean.class, false);
    String tsvFilename = args.getOptional("tsv", String.class, "tmp_result.tsv");
    tsvFilePath = Path.of(tsvFilename);
    tsvStrBuilder = new StringBuilder();
    tsvNeq = args.getOptional("tsv_neq", boolean.class, false);

    testCases = Path.of(args.getOptional("i", "cases", String.class, "wtune_data/calcite/calcite_tests"));
    // verbose = args.getOptional("v", "verbose", boolean.class, false);

    if (!Files.exists(testCases)) throw new IllegalArgumentException("no such file: " + testCases);

    String appName = args.getOptional("app", String.class, CALCITE_APP_NAME);
    app = App.of(appName);
    targetPairId = args.getOptional("target", Integer.class, -1);
    String skipStr = args.getOptional("skip", String.class, "");
    skipPairIds = Arrays.stream(skipStr.split(","))
            .filter(s -> !s.isBlank())
            .map(Integer::valueOf)
            .toList();
    rounds = args.getOptional("rounds", Integer.class, 5);
    if (rounds <= 0) {
      throw new IllegalArgumentException("rounds should be positive");
    }
    String outStr = args.getOptional("out", String.class, null);
    if (outStr != null) {
      outPath = Path.of(outStr);
      outStrBuilder = new StringBuilder();
    }
  }

  // 1=pass, 0=fail, -1=silent_fail
  // collect the result
  private void caseResult(int caseId, int result, long thisTime,
                        HashMap<String, List<Integer>> statistics) {
    if (result != 1) {
      if (result == 0) {
        if (time)
          println("Case " + caseId + " is: " + "NEQ " + thisTime + " ms");
        else
          println("Case " + caseId + " is: " + "NEQ");
      }
      statistics.computeIfAbsent("NEQ", k -> new ArrayList<>()).add(caseId);
    } else {
      if (time)
        println("Case " + caseId + " is: " + "EQ " + thisTime + " ms");
      else
        println("Case " + caseId + " is: " + "EQ");
      statistics.computeIfAbsent("EQ", k -> new ArrayList<>()).add(caseId);
    }
    if (time) {
      // only output .tsv when -time is set
      if (result == 1 || tsvNeq)
        tsvStrBuilder.append(thisTime);
      tsvStrBuilder.append('\n');
    }
  }

  // 1=pass, 0=fail, -1=silent_fail
  // verify a pair once
  private int verifyPair(QueryPair pair, int targetId) {
    final boolean verbose = false;
    if (verbose) System.out.println(pair.sql0 + "\n" + pair.sql1);
    // Some special cases: VALUES
    if (pair.p0 == null || pair.p1 == null) {
      if (pair.sql0.contains("VALUES") || pair.sql1.contains("VALUES")) {
        final String result = getCalciteVerifyResultConcrete(pair, verbose);
        // System.out.println("Case " + pair.pairId() + " is: " + result);
        // statistics.computeIfAbsent(result, k -> new ArrayList<>()).add(pair.pairId());
        return "EQ".equals(result) ? 1 : 0;
      } else {
        // cannot process other cases currently
        // statistics.computeIfAbsent("Cannot parse plan", k -> new ArrayList<>()).add(pair.pairId());
        // "cannot parse" is regarded as NEQ
        return 0;
      }
    }
    if (isSemanticError(pair.p0, pair.p1)) {
      return 1;
    }
    // case: totally the same
    if (isLiteralEq(pair.p0, pair.p1)) {
      return 1;
    }

    //if (targetId > 0) LogicSupport.setDumpLiaFormulas(true);

    final String res1 = getCalciteVerifyResultConcrete(pair, verbose);
    if (res1.equals("EQ")) {
      return 1;
    }

    return 0;
  }

  @Override
  public void run() throws Exception {
    long totalTime = 0; // EQ & NEQ cases time
    long totalTimeEQ = 0; // EQ cases time
    List<Long> timeEqCases = new ArrayList<>(); // running time of each EQ case
    final List<QueryPair> queryPairs = readPairs(Files.readAllLines(testCases));
    final int targetId = targetPairId, startId = -1;
    final HashMap<String, List<Integer>> statistics = new HashMap<>();
    statistics.put("EQ", new ArrayList<>());
    statistics.put("NEQ", new ArrayList<>());
    final Set<Integer> blacklist = new HashSet<>(skipPairIds);
    for (QueryPair pair : queryPairs) {
      if (targetId > 0 && pair.pairId() != targetId) continue;
      if (targetId < 0 && startId > 0 && pair.pairId() < startId) continue;
      if (blacklist.contains(pair.pairId())) {
//        statistics.computeIfAbsent("NEQ", k -> new ArrayList<>()).add(pair.pairId());
        if (time) tsvStrBuilder.append('\n');
        continue;
      }

      SqlSolver.initialize();
      QueryUExprICRewriter.selectIC(-1);

      thisTime = 0;
      long millisBefore = System.currentTimeMillis();
      int ret = verifyPair(pair, targetId);
      long millisAfter = System.currentTimeMillis();
      thisTime += millisAfter - millisBefore;
      if (time) {
        if (ret == 1 || tsvNeq) {
          millisBefore = System.currentTimeMillis();
          // thisTime will accumulate, and at last we take average
          for (int i = 1; i < rounds; i++) {
            verifyPair(pair, targetId);
          }
          millisAfter = System.currentTimeMillis();
          thisTime += millisAfter - millisBefore;
          thisTime /= rounds;
        }
        if (ret == 1) {
          totalTimeEQ += thisTime;
          timeEqCases.add(thisTime);
        }
        totalTime += thisTime;
      }
      caseResult(pair.pairId(), ret, thisTime, statistics);

    }

    // output .tsv
    if (time) Files.writeString(tsvFilePath, tsvStrBuilder);

    // find median
    final int eqCount = statistics.get("EQ").size();
    long medianEQ = 0;
    if (time) {
      timeEqCases.sort(Long::compare);
      if (eqCount == 0)
        medianEQ = -1;
      else if (eqCount % 2 == 0)
        medianEQ = (timeEqCases.get(eqCount / 2) + timeEqCases.get(eqCount / 2 - 1)) / 2;
      else
        medianEQ = timeEqCases.get(eqCount / 2);
    }

    for (Map.Entry<String, List<Integer>> entry : statistics.entrySet()) {
      println(entry.getKey() + ": " + entry.getValue().size());
      println(entry.getValue() + "\n");
    }

    /*if (time) {
      System.out.println("Total time (millisecond): " + totalTime);
      if (eqCount > 0) {
        System.out.println("Total time of passed cases (millisecond): " + totalTimeEQ);
        System.out.println("Average time of passed cases (millisecond): " + totalTimeEQ / eqCount);
        System.out.println("Median time of passed cases (millisecond): " + medianEQ);
      }
    }*/
    println("Passed " + eqCount + " cases.");

    // output
    if (outPath != null)
      Files.writeString(outPath, outStrBuilder);
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

  private List<QueryPair> readPairs(List<String> lines) {
    final Schema schema = app.schema("base");
    SqlNodePreprocess.setSchema(schema);
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

      if (q0 == null || q1 == null) {
        pairs.add(new QueryPair(i + 1, schema, sql0, sql1));
        continue;
      }

      q0.context().setSchema(schema);
      q1.context().setSchema(schema);
      NormalizationSupport.normalizeAst(q0);
      NormalizationSupport.normalizeAst(q1);

      final PlanContext p0 = assemblePlan(q0, schema);
      if (p0 == null) {
        final int ruleId = (i + 1) + 1 >> 1;
        //System.err.printf("Rule id: %d has wrong query at line %d \n", ruleId, i + 1);
        //System.err.println(getLastError());
        pairs.add(new QueryPair(i + 1, schema, sql0, sql1, q0, q1));
        continue;
      }
      final PlanContext p1 = assemblePlan(q1, schema);
      if (p1 == null) {
        final int ruleId = (i + 1) + 1 >> 1;
        //System.err.printf("Rule id: %d has wrong query at line %d \n", ruleId, i + 2);
        //System.err.println(getLastError());
        pairs.add(new QueryPair(i + 1, schema, sql0, sql1, q0, q1));
        continue;
      }

      pairs.add(new QueryPair(i + 1, schema, sql0, sql1, q0, q1, p0, p1));
    }

    return pairs;
  }

  private String getCalciteVerifyResultConcrete(QueryPair pair, boolean verbose) {
    try {
      if (pair.sql0.contains("VALUES") || pair.sql1.contains("VALUES")) {
        final UExprConcreteTranslationResult uExprs
            = UExprSupport.translateQueryWithVALUESToUExpr(pair.sql0, pair.sql1, pair.schema, 0);
        if (uExprs == null) return LogicSupport.stringifyResult(NEQ);
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

}

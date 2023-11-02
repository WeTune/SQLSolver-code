package wtune.superopt.runner;

import wtune.common.utils.Args;
import wtune.common.utils.IOSupport;
import wtune.common.utils.Lazy;
import wtune.sql.SqlSupport;
import wtune.sql.ast.SqlNode;
import wtune.sql.plan.PlanContext;
import wtune.sql.plan.PlanSupport;
import wtune.sql.schema.Schema;
import wtune.sql.support.action.NormalizationSupport;
import wtune.stmt.App;
import wtune.superopt.logic.LogicSupport;
import wtune.superopt.optimizer.OptimizationStep;
import wtune.superopt.optimizer.Optimizer;
import wtune.superopt.optimizer.OptimizerSupport;
import wtune.superopt.substitution.Substitution;
import wtune.superopt.substitution.SubstitutionBank;
import wtune.superopt.substitution.SubstitutionSupport;
import wtune.superopt.uexpr.UExprSupport;
import wtune.superopt.uexpr.UExprTranslationResult;

import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static java.time.format.DateTimeFormatter.ofPattern;
import static wtune.common.utils.Commons.joining;
import static wtune.common.utils.IOSupport.checkFileExists;
import static wtune.common.utils.IOSupport.io;
import static wtune.common.utils.IterableSupport.any;
import static wtune.sql.SqlSupport.parseSql;
import static wtune.common.datasource.DbSupport.MySQL;
import static wtune.sql.plan.PlanSupport.*;

public class RunCalciteCasesWeTune implements Runner {
  private String target;
  private Path testCasesPath, templatesPath, rulesPath;
  private Path outDir, outOpt;
  private App app;
  private int verbosity;
  private Lazy<SubstitutionBank> rules;
  private Lazy<List<QueryPair>> queryPairs;
  private boolean time, tsvNeq;

  private Path tsvFilePath;
  private StringBuilder tsvStrBuilder;

  private interface Task {
    void execute(RunCalciteCasesWeTune runner) throws Exception;
  }

  private static final Map<String, Task> TASKS =
      Map.of(
          "VerifyRule",
          RunCalciteCasesWeTune::verifyRule,
          "VerifyQuery",
          RunCalciteCasesWeTune::verifyQuery,
          "GenerateRewritings",
          RunCalciteCasesWeTune::generateRewritings);

  @Override
  public void prepare(String[] argStrings) throws Exception {
    final Args args = Args.parse(argStrings, 1);
    final Path dataDir = RunnerSupport.dataDir();
    final Path parentDir = dataDir.resolve(args.getOptional("D", "dir", String.class, "calcite"));
    final String subDirSuffix = LocalDateTime.now().format(ofPattern("MMddHHmmss"));

    time = args.getOptional("time", boolean.class, false);
    String tsvFilename = args.getOptional("tsv", String.class, "tmp_result.tsv");
    tsvFilePath = Path.of(tsvFilename);
    tsvStrBuilder = new StringBuilder();
    tsvNeq = args.getOptional("tsv_neq", boolean.class, false);

    outDir = parentDir.resolve("run" + subDirSuffix);
    outOpt = outDir.resolve("1_query.tsv");

    String appName = args.getOptional("A", "app", String.class, "calcite_test");
    app = App.of(appName);
    target = args.getOptional("T", "task", String.class, "all");
    verbosity = args.getOptional("v", "verbose", int.class, 0);

    if (!target.equals("all") && !TASKS.containsKey(target))
      throw new IllegalArgumentException("no such task: " + target);

    final String testCasesFile = args.getOptional("i", "input", String.class, "calcite_tests");
    final String tempsFile = args.getOptional("t", "templates", String.class, "calcite_templates");
    final String rulesFile = args.getOptional("R", "rules", String.class, "rules/rules.txt");
    testCasesPath = parentDir.resolve(testCasesFile);
    templatesPath = parentDir.resolve(tempsFile);
    rulesPath = dataDir.resolve(rulesFile);

    rules = Lazy.mk(io(() -> SubstitutionSupport.loadBank(rulesPath)));
    queryPairs = Lazy.mk(io(() -> readPairs(Files.readAllLines(testCasesPath))));
  }

  @Override
  public void run() throws Exception {
    if (target.equals("all")) {
      for (var pair : TASKS.entrySet()) {
        System.out.println("Begin: " + pair.getKey());
        pair.getValue().execute(this);
      }
    } else {
      TASKS.get(target).execute(this);
    }
  }

  long nano2millis(long nano) {
    return nano / 1000000;
  }

  private void verifyQuery() throws IOException {
    checkFileExists(templatesPath);
    final List<String> lines = Files.readAllLines(templatesPath);
    int i = 0;
    for (String line : lines) {
      ++i;
      if (line.isEmpty() || !Character.isDigit(line.charAt(0))) continue;
      final String[] fields = line.split("\s+", 2);
      if (fields.length != 2) {
        if (verbosity >= 1) System.err.println("unrecognized template at line: " + i);
        continue;
      }

      try {
        final Substitution rule = Substitution.parse(fields[1]);
        final UExprTranslationResult uExpr = UExprSupport.translateToUExpr(rule);
        final int result = LogicSupport.proveEq(uExpr);
        System.out.println(fields[0] + ": " + LogicSupport.stringifyResult(result));
        System.out.println("  rule: " + rule);

      } catch (Throwable ex) {
        if (verbosity >= 1) System.err.println("unrecognized template at line: " + i);
        if (verbosity >= 2) ex.printStackTrace();
      }
    }
    System.out.println("Verified " + i + " queries.");
  }

  private static final int ROUNDS = 5;

  /** Note that this method returns time in nanoseconds. */
  private long verifyPair(SubstitutionBank rules, QueryPair pair) {
    long nanos_before;
    long nanos_after;
    final Optimizer opt0 = Optimizer.mk(rules);
    final Optimizer opt1 = Optimizer.mk(rules);
    //      opt0.setTracing(true);
    //      opt1.setTracing(true);
    nanos_before = System.nanoTime();
    final Set<PlanContext> rewritten0 = opt0.optimize(pair.p0);
    final Set<PlanContext> rewritten1 = opt1.optimize(pair.p1);

    for (PlanContext plan0 : rewritten0)
      for (PlanContext plan1 : rewritten1)
        if (isLiteralEq(plan0, plan1)) {
          nanos_after = System.nanoTime();
          if (verbosity >= 1) {
            System.out.println("Both are rewritten to: ");
          }
          long thisTime = nanos_after - nanos_before;
          // System.out.println("  " + translateAsAst(plan0, plan0.root(), false));
          return thisTime;
        }
    nanos_after = System.nanoTime();
    long thisTime = nanos_after - nanos_before;
    return -1 - thisTime; // make sure the return value of NEQ is negative
  }

  private int lastPairId = 0;
  private void appendTSV(int pairId, boolean eq, long thisTime) {
    // append empty lines
    for (int i = lastPairId + 1; i < pairId; i++) {
      tsvStrBuilder.append('\n');
    }
    lastPairId = pairId;
    // append the new record
    if (eq || tsvNeq)
      tsvStrBuilder.append(nano2millis(thisTime));
    tsvStrBuilder.append('\n');
  }

  private long neqTime(long ret) {
    return (-1 - ret);
  }

  private void verifyRule() {
    // System.out.println("verifyRule");
    checkFileExists(testCasesPath);
    checkFileExists(rulesPath);
    OptimizerSupport.setOptimizerTweaks(
        OptimizerSupport.TWEAK_KEEP_ORIGINAL_PLAN | OptimizerSupport.TWEAK_SORT_FILTERS_DURING_REWRITE | OptimizerSupport.TWEAK_PERMUTE_JOIN_TREE);

    final SubstitutionBank rules = this.rules.get();
    final List<QueryPair> pairs = this.queryPairs.get();
    System.out.println("Recognized " + pairs.size() + " pairs of SQL.");

    int eqCount = 0;
    long totalTime = 0, totalTimeEQ = 0;
    List<Long> timeEqCases = new ArrayList<>();
    for (final QueryPair pair : pairs) {
      long thisTime = verifyPair(rules, pair);
      boolean eq = thisTime >= 0;
      if (time) {
        if (eq) {
          // EQ, run ROUNDS times
          for (int i = 1; i < ROUNDS; i++) {
            thisTime += verifyPair(rules, pair);
          }
          thisTime /= ROUNDS;
        } else if (tsvNeq) {
          // NEQ but tsvNeq, run ROUNDS times
          thisTime = neqTime(thisTime);
          for (int i = 1; i < ROUNDS; i++) {
            thisTime += neqTime(verifyPair(rules, pair));
          }
          thisTime /= ROUNDS;
        } else {
          // NEQ and not tsvNeq, run once
          thisTime = neqTime(thisTime);
        }
        // thisTime should be the average or one-time running time here
        if (eq) {
          totalTimeEQ += thisTime;
          timeEqCases.add(thisTime);
        }
        totalTime += thisTime;
        appendTSV(pair.pairId(), eq, thisTime);
      }
      if (eq) {
        ++eqCount;
        if (time)
          System.out.println("case " + pair.pairId() + " pass: " + nano2millis(thisTime) + " ms");
        else
          System.out.println("case " + pair.pairId() + " pass");
      }
    }

    // output .tsv
    try {
      if (time) Files.writeString(tsvFilePath, tsvStrBuilder);
    } catch (Exception e) {
      e.printStackTrace();
    }

    // find median
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

    // nano -> millis
    /*if (time) {
      System.out.println("Total time (millisecond): " + nano2millis(totalTime));
      if (eqCount > 0) {
        System.out.println("Total time of passed cases (millisecond): " + nano2millis(totalTimeEQ));
        System.out.println("Average time of passed cases (millisecond): " + nano2millis(totalTimeEQ / eqCount));
        System.out.println("Median time of passed cases (millisecond): " + nano2millis(medianEQ));
      }
    }*/
    System.out.println("Passed " + eqCount + " cases.");
  }

  private void generateRewritings() throws IOException {
    // System.out.println("generateRewriting");
    OptimizerSupport.setOptimizerTweaks(0);
    checkFileExists(testCasesPath);
    checkFileExists(rulesPath);
    if (!Files.exists(outDir)) Files.createDirectories(outDir);

    final SubstitutionBank rules = this.rules.get();
    if(rules.isExtended()) OptimizerSupport.addOptimizerTweaks(OptimizerSupport.TWEAK_ENABLE_EXTENSIONS);

    final List<QueryPair> pairs = this.queryPairs.get();

    for (final QueryPair pair : pairs) {
      final Optimizer opt0 = Optimizer.mk(rules);
      final Optimizer opt1 = Optimizer.mk(rules);
      opt0.setTracing(true);
      opt1.setTracing(true);
      final Set<PlanContext> rewritten0 = opt0.optimize(pair.p0);
      final Set<PlanContext> rewritten1 = opt1.optimize(pair.p1);

      IOSupport.appendTo(outOpt, writer -> dumpRewritten(writer, pair, 0, opt0, rewritten0));
      IOSupport.appendTo(outOpt, writer -> dumpRewritten(writer, pair, 1, opt1, rewritten1));
    }
  }

  private static class QueryPair {
    private final int lineNum;
    private final SqlNode q0, q1;
    private final PlanContext p0, p1;

    private QueryPair(int lineNum, SqlNode q0, SqlNode q1, PlanContext p0, PlanContext p1) {
      this.lineNum = lineNum;
      this.q0 = q0;
      this.q1 = q1;
      this.p0 = p0;
      this.p1 = p1;
    }

    private int id0() {
      return lineNum;
    }

    private int id1() {
      return lineNum + 1;
    }

    private int pairId() {
      return lineNum + 1 >> 1;
    }
  }

  private void dumpRewritten(
          PrintWriter out, QueryPair pair, int index, Optimizer opt, Set<PlanContext> rewrittenPlans) {
    if (rewrittenPlans.isEmpty()) return;

    int i = 0;
    for (PlanContext plan : rewrittenPlans) {
      final SqlNode sqlNode0 = translateAsAst(plan, plan.root(), false);
      final List<OptimizationStep> traces = opt.traceOf(plan);
      final String str = joining(",", traces, it -> String.valueOf(it.ruleId()));
      out.printf(
          "%s\t%d\t%d\t%s\t%s\n", "calcite_test", index == 0 ? pair.id0() : pair.id1(), i++, sqlNode0, str);
    }
  }

  private void dumpTrace(
      PrintWriter out,
      QueryPair pair,
      int index,
      Optimizer optimizer,
      Set<PlanContext> rewrittenPlans) {
    if (rewrittenPlans.isEmpty()) return;

    int i = 0;
    for (PlanContext plan : rewrittenPlans) {
      final List<OptimizationStep> traces = optimizer.traceOf(plan);
      final String str = joining(",", traces, it -> String.valueOf(it.ruleId()));
      out.printf("%s-%d\t%d\t%s\n", "calcite_test", index == 0 ? pair.id0() : pair.id1(), i++, str);

      if (rules.get().isExtended() && any(traces, step -> step.rule() != null && step.rule().isExtended())) {
        final int stmtId = pair.lineNum + index;
        final SqlNode ast = index == 0 ? pair.q0 : pair.q1;
        System.out.println("calcite_tests\t" + stmtId + "\t" + ast
                           + "\t" + translateAsAst(plan, plan.root(), false)
                           + "\t" + str);
        break;
      }
    }
  }

  private List<QueryPair> readPairs(List<String> lines) {
    final Schema schema = app.schema("base");
    SqlSupport.muteParsingError();

    final List<QueryPair> pairs = new ArrayList<>(lines.size() >> 1);
    for (int i = 0, bound = lines.size(); i < bound; i += 2) {
//        if (i != 92) continue;
      final String first = lines.get(i), second = lines.get(i + 1);
      final SqlNode q0 = parseSql(MySQL, first);
      final SqlNode q1 = parseSql(MySQL, second);

      if (q0 == null || !PlanSupport.isSupported(q0)) {
        if (verbosity >= 2) System.err.printf("unsupported query at line %d: %s \n", i + 1, first);
        continue;
      }
      if (q1 == null || !PlanSupport.isSupported(q1)) {
        if (verbosity >= 2) System.err.printf("unsupported query at line %d: %s \n", i + 2, second);
        continue;
      }

      q0.context().setSchema(schema);
      q1.context().setSchema(schema);
      NormalizationSupport.normalizeAst(q0);
      NormalizationSupport.normalizeAst(q1);

      final PlanContext p0 = assemblePlan(q0, schema);
      if (p0 == null) {
        if (verbosity >= 2) {
          System.err.printf("wrong query at line %d: %s\n", i + 1, first);
          System.err.println(getLastError());
        }
        continue;
      }
      final PlanContext p1 = assemblePlan(q1, schema);
      if (p1 == null) {
        if (verbosity >= 2) {
          System.err.printf("wrong query at line %d: %s\n", i + 2, second);
          System.err.println(getLastError());
        }
        continue;
      }

      pairs.add(new QueryPair(i + 1, q0, q1, p0, p1));
    }

    return pairs;
  }
}

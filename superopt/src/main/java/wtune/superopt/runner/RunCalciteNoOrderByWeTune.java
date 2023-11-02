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

public class RunCalciteNoOrderByWeTune implements Runner {
  private String target;
  private Path testCasesPath, testTagsPath, templatesPath, rulesPath;
  private Path outDir, outOpt;
  private App app;
  private int verbosity;
  private Lazy<SubstitutionBank> rules;
  private Lazy<List<QueryPair>> queryPairs;
  private boolean time;
  private long totalTime;

  private interface Task {
    void execute(RunCalciteNoOrderByWeTune runner) throws Exception;
  }

  private static final Map<String, Task> TASKS =
      Map.of(
          "VerifyRule",
          RunCalciteNoOrderByWeTune::verifyRule,
          "VerifyQuery",
          RunCalciteNoOrderByWeTune::verifyQuery,
          "GenerateRewritings",
          RunCalciteNoOrderByWeTune::generateRewritings);

  @Override
  public void prepare(String[] argStrings) throws Exception {
    final Args args = Args.parse(argStrings, 1);
    final Path dataDir = RunnerSupport.dataDir();
    final Path parentDir = dataDir.resolve(args.getOptional("D", "dir", String.class, "calcite"));
    final String subDirSuffix = LocalDateTime.now().format(ofPattern("MMddHHmmss"));

    time = args.getOptional("time", boolean.class, false);

    outDir = parentDir.resolve("run" + subDirSuffix);
    outOpt = outDir.resolve("1_query.tsv");

    String appName = args.getOptional("A", "app", String.class, "calcite_test");
    app = App.of(appName);
    target = args.getOptional("T", "task", String.class, "all");
    verbosity = args.getOptional("v", "verbose", int.class, 0);

    if (!target.equals("all") && !TASKS.containsKey(target))
      throw new IllegalArgumentException("no such task: " + target);

    final String testCasesFile = args.getOptional("i", "input", String.class, "tests");
    final String testTagsFile = args.getOptional("l", "tag", String.class, "tags");
    final String tempsFile = args.getOptional("t", "templates", String.class, "calcite_templates");
    final String rulesFile = args.getOptional("R", "rules", String.class, "rules/rules.txt");
    testCasesPath = parentDir.resolve(testCasesFile);
    testTagsPath = parentDir.resolve(testTagsFile);
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

  // should make sure that all pairs do not contain syntax errors so that any of the pairs are not skipped
  private List<Integer> pairTags = null;
  private boolean pairTagsFallback = false;

  private int getPairTag(int index) {
    if (pairTags == null) {
      pairTags = new ArrayList<>();
      try {
        List<String> lines = Files.readAllLines(testTagsPath);
        for (String line : lines) {
          pairTags.add(Integer.valueOf(line));
	}
      } catch (Exception e) {
        // fallback
        pairTagsFallback = true;
      }
    }
    if (pairTagsFallback) return index;
    return pairTags.get(index);
  }

  private void printPairResult(int index, boolean success) {
    int tag = getPairTag(index);
    System.out.println("case " + tag + (success ? " pass" : " fail"));
  }

  private void verifyRule() {
    // System.out.println("verifyRule");
    checkFileExists(testCasesPath);
    checkFileExists(rulesPath);
    OptimizerSupport.setOptimizerTweaks(
        OptimizerSupport.TWEAK_KEEP_ORIGINAL_PLAN | OptimizerSupport.TWEAK_SORT_FILTERS_DURING_REWRITE | OptimizerSupport.TWEAK_PERMUTE_JOIN_TREE);

    final SubstitutionBank rules = this.rules.get();
    final List<QueryPair> pairs = this.queryPairs.get();

    int count = 0, pairIndex = 0;
    long millis_before;
    long millis_after;
    outer:
    for (final QueryPair pair : pairs) {
      if (pair == null) {
        printPairResult(pairIndex++, false);
        continue;
      }
      final Optimizer opt0 = Optimizer.mk(rules);
      final Optimizer opt1 = Optimizer.mk(rules);
      //      opt0.setTracing(true);
      //      opt1.setTracing(true);
      millis_before = System.currentTimeMillis();
      final Set<PlanContext> rewritten0 = opt0.optimize(pair.p0);
      final Set<PlanContext> rewritten1 = opt1.optimize(pair.p1);

      for (PlanContext plan0 : rewritten0)
        for (PlanContext plan1 : rewritten1)
          if (isLiteralEq(plan0, plan1)) {
            millis_after = System.currentTimeMillis();
            //            OptimizerSupport.dumpTrace(opt0, plan0);
            //            OptimizerSupport.dumpTrace(opt1, plan1);
            ++count;
            // System.out.printf("%d,%d\n", pair.lineNum, pair.lineNum + 1);
            if (verbosity >= 1) {
              System.out.println("Both are rewritten to: ");
//              System.out.println(translateAsAst(plan0, plan0.root(), false));
            }
            long thisTime = millis_after - millis_before;
            totalTime += thisTime;
            printPairResult(pairIndex++, true);
            // System.out.println("  " + translateAsAst(plan0, plan0.root(), false))
            continue outer;
          }

      // fail to verify
      printPairResult(pairIndex++, false);
    }

    if(time) {
      System.out.println("Total time (millisecond): " + totalTime);
      System.out.println("Pass total time (millisecond): " + totalTime);
      System.out.println("Pass case count : " + count);
      System.out.println("Pass average time (millisecond):" + totalTime / count);
    }
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
        pairs.add(null);
        continue;
      }
      if (q1 == null || !PlanSupport.isSupported(q1)) {
        if (verbosity >= 2) System.err.printf("unsupported query at line %d: %s \n", i + 2, second);
        pairs.add(null);
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

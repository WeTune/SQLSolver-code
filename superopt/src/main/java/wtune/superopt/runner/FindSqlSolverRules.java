package wtune.superopt.runner;

import wtune.common.utils.Args;
import wtune.common.utils.IOSupport;
import wtune.common.utils.IterableSupport;
import wtune.sql.SqlSupport;
import wtune.sql.ast.SqlNode;
import wtune.sql.ast.constants.JoinKind;
import wtune.sql.plan.JoinNode;
import wtune.sql.plan.PlanContext;
import wtune.sql.plan.PlanKind;
import wtune.sql.plan.ProjNode;
import wtune.sql.schema.Schema;
import wtune.sql.support.action.NormalizationSupport;
import wtune.stmt.App;
import wtune.superopt.logic.LogicSupport;
import wtune.superopt.logic.SqlSolver;
import wtune.superopt.substitution.Substitution;
import wtune.superopt.substitution.SubstitutionBank;
import wtune.superopt.substitution.SubstitutionSupport;
import wtune.superopt.uexpr.UExprConcreteTranslationResult;
import wtune.superopt.uexpr.UExprSupport;
import wtune.superopt.uexpr.UExprTranslationResult;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.*;
import java.util.stream.IntStream;

import static wtune.common.datasource.DbSupport.MySQL;
import static wtune.sql.SqlSupport.parseSql;
import static wtune.sql.plan.PlanSupport.*;
import static wtune.superopt.logic.LogicSupport.*;

public class FindSqlSolverRules implements Runner {
  private static final String CALCITE_APP_NAME = "calcite_test";

  private Path ruleFilePath;

  private static List<Integer> blackList = List.of(127, 203, 229, 255, 281, 353, 395, 463);

  @Override
  public void prepare(String[] argStrings) {
    final Args args = Args.parse(argStrings, 1);
    final Path dataDir = RunnerSupport.dataDir();

    // ruleFilePath = Path.of(args.getOptional("i", "cases", String.class, "wtune_data/calcite/calcite_tests"));
    ruleFilePath = dataDir.resolve("prepared").resolve("rules.sqlsolver.txt");
    System.out.println(ruleFilePath);

    if (!Files.exists(ruleFilePath)) throw new IllegalArgumentException("no such file: " + ruleFilePath);

  }

  @Override
  public void run() throws Exception {
    final SubstitutionBank rules = SubstitutionSupport.loadBank(ruleFilePath);
    for (Substitution rule : rules.rules()) {
        final UExprTranslationResult uExprs =
          UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
        final int result = LogicSupport.proveEqByLIAStar2(rule);
        System.out.println("Rule id: " + rule.id() + " is " + LogicSupport.stringifyResult(result));
    }
  }

}

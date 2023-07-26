package wtune.superopt.logic;

import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;
import wtune.common.utils.IOSupport;
import wtune.superopt.substitution.Substitution;
import wtune.superopt.substitution.SubstitutionBank;
import wtune.superopt.substitution.SubstitutionSupport;
import wtune.superopt.uexpr.UExprSupport;
import wtune.superopt.uexpr.UExprTranslationResult;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static wtune.superopt.TestHelper.dataDir;

@Tag("fol")
@Tag("fast")
public class ExistingRuleTest {

  @Test
  public void dumpUexpr() throws IOException {
    final Path ruleFilePath = dataDir().resolve("prepared").resolve("rules.example.txt");
    final Path outPath = dataDir().resolve("logic").resolve("rules.example2.tsv");
    if (!Files.exists(outPath)) {
      Files.createDirectories(outPath.getParent());
      Files.createFile(outPath);
    }

    final SubstitutionBank rules = SubstitutionSupport.loadBank(ruleFilePath);
    final int startRuleId = 1;
    for (Substitution rule : rules.rules()) {
      if (rule.id() > 31) break;
      if (rule.id() < startRuleId) continue;
      // System.out.println(rule.id());
      // System.out.println(rule);
      final UExprTranslationResult uExprs = UExprSupport.translateToUExpr(rule);
      // System.out.println("  [[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
      // System.out.println("  [[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
      //IOSupport.appendTo(
      //    outPath,
      //    writer ->
      //        writer.printf(
      //            "%s\t%s\t%s\n",
      //            rule.toString(), uExprs.sourceExpr().toString(), uExprs.targetExpr().toString()));
      // LogicSupport.setDumpFormulas(true);
      final int result = LogicSupport.proveEq(uExprs);
      System.out.println("Rule-" + rule.id() + ": " + LogicSupport.stringifyResult(result));
      // assertEquals(LogicSupport.EQ, result, rule.toString());
    }
  }
}

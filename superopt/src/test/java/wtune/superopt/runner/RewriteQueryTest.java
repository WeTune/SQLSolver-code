package wtune.superopt.runner;

import org.junit.jupiter.api.Test;
import wtune.common.utils.IOSupport;
import wtune.sql.plan.PlanContext;
import wtune.sql.plan.PlanKind;
import wtune.stmt.Statement;
import wtune.superopt.fragment.Fragment;
import wtune.superopt.logic.LogicSupport;
import wtune.superopt.substitution.Substitution;
import wtune.superopt.substitution.SubstitutionBank;
import wtune.superopt.substitution.SubstitutionSupport;
import wtune.superopt.uexpr.UExprSupport;
import wtune.superopt.uexpr.UExprTranslationResult;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;

import static org.junit.jupiter.api.Assertions.*;
import static wtune.superopt.TestHelper.dataDir;

class RewriteQueryTest {

  @Test
  void run() throws Exception {

//    Statement stmt = Statement.mk("broadleaf", 1, "select blc_sku.cost from blc_sku where blc_sku.cost = 3", "stackTrace");
//    RewriteQuery rq = new RewriteQuery();
//    rq.prepare(new String[0]);
//    rq.optimizeOne(stmt);

    int cnt = 0;
    int targetId = -1;
    try {
      final Path dataDir = RunnerSupport.dataDir();
      final String ruleFileName = "rules.sqlsolver.nonreduce.txt";
      final Path ruleFilePath = dataDir.resolve(ruleFileName);
      IOSupport.checkFileExists(ruleFilePath);
      SubstitutionBank rules = SubstitutionSupport.loadBank(ruleFilePath);
      for (Substitution rule : rules.rules()) {
        if(targetId > 0 && rule.id() != targetId) continue;
//        System.out.println(rule);
        updateRuleFile(rule, "./Project/wtune-code/wtune_data/prepared/rules.test.txt");
//        boolean b1 = rewriteRUle(true, rule);
        boolean b2 = rewriteRUle(false, rule);
        if (b2 == false) {
          System.out.println("cannot apply rule " + rule.id());
          cnt++;
        }
      }
    } catch (Exception e) {
      e.printStackTrace();
    }
    System.out.println("totally " + cnt + " rules");
  }

  boolean rewriteRUle(boolean b, Substitution rule) {
    try {
      var planPair = (b) ? SubstitutionSupport.translateAsPlan(rule) : SubstitutionSupport.translateAsPlan2(rule);
      RewriteQuery rq = new RewriteQuery();
      rq.prepare(new String[0]);
      PlanContext plan = planPair.getLeft();
      if(plan.kindOf(plan.root()) == PlanKind.Filter )
        return true;
      return rq.myRun(plan);
    } catch (RuntimeException e) {
      if (b == false)
        return true;
      else
        return false;
    }
    catch (Exception e) {
      if (b == false)
        return true;
      else
        return false;
    }
  }

  @Test
  void updateRuleFile(Substitution rule, String fileName) {
    try {
      File f = new File(fileName);
      f.delete();
      String s = rule.toString();
      BufferedWriter out = new BufferedWriter(new FileWriter(fileName));
      out.write(s);
      out.close();
    } catch (Exception e) {
      e.printStackTrace();
    }
  }

  boolean redundantRule(Substitution rule, HashSet<Substitution> existingRules) {
    for(Substitution s : existingRules) {
      String thisRule = rule._0().toString() + rule._1().toString();
      String thatRule = s._0().toString() + s._1().toString();
      if(thatRule.equals(thisRule))
        return true;
    }
    return false;
  }

  boolean isUseful0(Substitution rule) {
    Fragment q0 = rule._0();
    Fragment q1 = rule._1();
    return (q0.toString().indexOf("Agg") > 0 &&
//        q0.toString().indexOf("Agg") < 0 &&
        q1.toString().indexOf("Agg") < 0);
  }

  boolean isUseful1(Substitution rule) {
    Fragment q0 = rule._0();
    Fragment q1 = rule._1();
    return (q0.toString().indexOf("Union") > 0 &&
        q1.toString().indexOf("Union") < 0);
  }

  @Test
  void testRuleFilter() throws IOException {
    final Path ruleFilePath = dataDir().resolve("prepared").resolve("rules.sqlsolver.txt");
    final SubstitutionBank rules = SubstitutionSupport.loadBank(ruleFilePath);
    int targetId = -1;
    int num = 0;
    HashSet<Substitution> usefulRules = new HashSet<>();
    for (Substitution rule : rules.rules()) {
      if(targetId > 0 && rule.id() != targetId) continue;
      if(redundantRule(rule, usefulRules)) continue;
//      if(isUseful0(rule)) {
//        usefulRules.add(rule);
//      }
      if(isUseful1(rule) && !isUseful0(rule)) {
        usefulRules.add(rule);
      }
//      if(usefulRules.size() > 10)
//        break;
    }

    for(Substitution rule : usefulRules) {
      System.out.println("" + rule.id() + "\t" + rule);
    }
  }
}
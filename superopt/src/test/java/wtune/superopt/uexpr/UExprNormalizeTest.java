package wtune.superopt.uexpr;

import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;
import wtune.superopt.substitution.Substitution;
import wtune.superopt.substitution.SubstitutionBank;
import wtune.superopt.substitution.SubstitutionSupport;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

@Tag("norm")
@Tag("fast")
public class UExprNormalizeTest {

  @Test
  public void testDistributeAdd() {
    final Substitution rule =
        Substitution.parse(
            "Proj<a2 s0>(LeftJoin<a0 a1>(Input<t0>,Input<t1>))|"
                + "Proj<a3 s1>(Input<t2>)|"
                + "AttrsSub(a0,t0);AttrsSub(a1,t1);AttrsSub(a2,t0);"
                + "Unique(t1,a1);TableEq(t2,t0);AttrsEq(a3,a2);SchemaEq(s1,s0)");
    final UExprTranslationResult uExprs = UExprSupport.translateToUExpr(rule);
    System.out.println(uExprs.sourceExpr());
  }

  @Test
  public void testCombineSquash() {
    final UVar var1 = UVar.mkBase(UName.mk("x1"));
    final UVar var2 = UVar.mkBase(UName.mk("x2"));
    final UVar var3 = UVar.mkBase(UName.mk("x3"));

    final UTerm squash1 = USquash.mk(UTable.mk(UName.mk("t1"), var1));
    final UTerm squash2 = USquash.mk(UTable.mk(UName.mk("t2"), var2));
    UTerm mul1 = UMul.mk(squash1, squash2);
    UExprSupport.normalizeExpr(mul1);
    System.out.println(mul1);

    final UTerm squash3 = USquash.mk(UTable.mk(UName.mk("t3"), var3));
    final UTerm mul2 = UMul.mk(squash1, squash2, squash3);
    final UTerm add = UAdd.mk(mul1, mul2);
    final UTerm sum = USum.mk(Set.of(var1, var2, var3), add);
    UExprSupport.normalizeExpr(sum);
    System.out.println(sum);
  }

  @Test
  void testNormalFormOfUsefulRules() throws IOException {
    final SubstitutionBank rules =
        SubstitutionSupport.loadBank(dataDir().resolve("prepared/rules.example.txt"));
    int targetId = 4;
    for (Substitution rule : rules.rules()) {
      // if (rule.id() != targetId) continue;
      if (rule.id() > 31) break;
      final UExprTranslationResult uExprs = UExprSupport.translateToUExpr(rule);
      // System.out.println("  [[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
      // System.out.println("  [[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
      assertTrue(
          UExprSupport.checkNormalForm(uExprs.sourceExpr())
              && UExprSupport.checkNormalForm(uExprs.targetExpr()),
          "Not SPNF for Uexpr of rule #" + rule.id());
    }
  }

  @Test
  void testNormalFormOfVerifiedRules() throws IOException {
    final SubstitutionBank rules =
        SubstitutionSupport.loadBank(dataDir().resolve("prepared/rules.txt"));
    for (Substitution rule : rules.rules()) {
      final UExprTranslationResult uExprs = UExprSupport.translateToUExpr(rule);
      assertTrue(
          UExprSupport.checkNormalForm(uExprs.sourceExpr())
              && UExprSupport.checkNormalForm(uExprs.targetExpr()),
          "Not SPNF for Uexpr of rule #" + rule.id());
    }
  }

  private static Path dataDir() {
    return Path.of(System.getProperty("wetune.data_dir", "wtune_data"));
  }
}

package wtune.superopt.uexpr;

import org.junit.jupiter.api.*;
import wtune.superopt.logic.LogicSupport;
import wtune.superopt.substitution.Substitution;
import wtune.superopt.substitution.SubstitutionBank;
import wtune.superopt.substitution.SubstitutionSupport;

import java.io.IOException;
import java.nio.file.Path;
import java.util.*;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static wtune.common.utils.IterableSupport.any;
import static wtune.superopt.TestHelper.dataDir;

@Tag("ic")
@Tag("fast")
@TestMethodOrder(MethodOrderer.OrderAnnotation.class)
public class UExprICRewriteTest {
  /** Useful rules # concerning integrity constraints: 2, 6, 7, 8, 9, 10, 11, 12, 15, 16, 24, 30 */
  @Test
  @Order(1)
  public void testUniqueSelfJoinWithSum() {
    /* Useful rule #16 */
    final Substitution rule =
        Substitution.parse(
            "Proj<a0 s0>(InnerJoin<k0 k1>(Input<t0>,Input<t1>))|"
                + "Proj<a1 s1>(Input<t2>)|"
                + "AttrsSub(a0,t0);AttrsSub(k0,t0);AttrsSub(k1,t1);"
                + "NotNull(t0,k0);NotNull(t1,k1);Unique(t0,k0);Unique(t1,k1);"
                + "TableEq(t0,t1);AttrsEq(k0,k1);SchemaEq(s1,s0);TableEq(t2,t0);AttrsEq(a1,a0)");
    final UExprTranslationResult uExprsRaw = UExprSupport.translateToUExpr(rule);
    System.out.println("Raw UExpressions: ");
    System.out.println("  [[q0]](" + uExprsRaw.sourceOutVar() + ") := " + uExprsRaw.sourceExpr());
    System.out.println("  [[q1]](" + uExprsRaw.targetOutVar() + ") := " + uExprsRaw.targetExpr());
    assertEquals(
        "∑{x0,x1}([x2 = a0(x0)] * t0(x0) * t0(x1) * [k0(x0) = k0(x1)] * not([IsNull(k0(x1))]))",
        uExprsRaw.sourceExpr().toString());
    assertEquals("∑{x0}([x2 = a0(x0)] * t0(x0))", uExprsRaw.targetExpr().toString());

    System.out.println("Rewritten UExpressions: ");
    final UExprTranslationResult uExprs =
        UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
    System.out.println("  [[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
    System.out.println("  [[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
    assertEquals("∑{x0}(||[x2 = a0(x0)] * t0(x0)||)", uExprs.sourceExpr().toString());
    assertEquals("∑{x0}(||[x2 = a0(x0)] * t0(x0)||)", uExprs.targetExpr().toString());
    final int result =
        LogicSupport.proveEq(uExprs, LogicSupport.PROVER_DISABLE_INTEGRITY_CONSTRAINTS_THEOREM);
    System.out.println("Prove result: " + LogicSupport.stringifyResult(result));
    assertEquals(LogicSupport.EQ, result, rule.toString());
  }

  @Test
  @Order(2)
  public void testUniqueSelfJoinWithoutSum() {
    /* Useful rule #30 */
    final Substitution rule =
        Substitution.parse(
            "Filter<p0 a2>(InnerJoin<a0 a1>(Input<t0>,Input<t1>))|"
                + "Filter<p1 a5>(InnerJoin<a3 a4>(Input<t2>,Input<t3>))|"
                + "AttrsSub(a0,t0);AttrsSub(a1,t1);AttrsSub(a2,t1);TableEq(t0,t1);AttrsEq(a0,a1);"
                + "Unique(t0,a0);Unique(t1,a1);"
                + "TableEq(t2,t0);TableEq(t3,t1);AttrsEq(a3,a0);AttrsEq(a4,a1);AttrsEq(a5,a2);"
                + "PredicateEq(p1,p0);AttrsSub(a5,t0)");
    final UExprTranslationResult uExprsRaw = UExprSupport.translateToUExpr(rule);
    System.out.println("Raw UExpressions: ");
    System.out.println("  [[q0]](" + uExprsRaw.sourceOutVar() + ") := " + uExprsRaw.sourceExpr());
    System.out.println("  [[q1]](" + uExprsRaw.targetOutVar() + ") := " + uExprsRaw.targetExpr());
    assertEquals(
        "t0(x0) * t0(x1) * [a0(x0) = a0(x1)] * not([IsNull(a0(x1))]) * [p0(a2(x1))]",
        uExprsRaw.sourceExpr().toString());
    assertEquals(
        "t0(x0) * t0(x1) * [a0(x0) = a0(x1)] * not([IsNull(a0(x1))]) * [p0(a2(x0))]",
        uExprsRaw.targetExpr().toString());

    System.out.println("Rewritten UExpressions: ");
    final UExprTranslationResult uExprs =
        UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
    System.out.println("  [[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
    System.out.println("  [[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
    assertEquals(
        "not([IsNull(a0(x1))]) * [p0(a2(x1))] * ||t0(x0) * [x0 = x1]||",
        uExprs.sourceExpr().toString());
    assertEquals(
        "not([IsNull(a0(x1))]) * ||t0(x0) * [x0 = x1] * [p0(a2(x0))]||",
        uExprs.targetExpr().toString());
    final int result =
        LogicSupport.proveEq(uExprs, LogicSupport.PROVER_DISABLE_INTEGRITY_CONSTRAINTS_THEOREM);
    System.out.println("Prove result: " + LogicSupport.stringifyResult(result));
    assertEquals(LogicSupport.EQ, result, rule.toString());
  }

  @Test
  @Order(3)
  public void testUniqueSquashOnDedup() {
    /* Useful rule #2 */
    final Substitution rule =
        Substitution.parse(
            "Proj*<a0 s0>(Input<t0>)|"
                + "Proj<a1 s1>(Input<t1>)|"
                + "AttrsSub(a0,t0);Unique(t0,a0);SchemaEq(s1,s0);TableEq(t1,t0);AttrsEq(a1,a0)");
    final UExprTranslationResult uExprsRaw = UExprSupport.translateToUExpr(rule);
    System.out.println("Raw UExpressions: ");
    System.out.println("  [[q0]](" + uExprsRaw.sourceOutVar() + ") := " + uExprsRaw.sourceExpr());
    System.out.println("  [[q1]](" + uExprsRaw.targetOutVar() + ") := " + uExprsRaw.targetExpr());
    assertEquals("∑{x0}([x1 = a0(x0)] * t0(x0))", uExprsRaw.sourceExpr().toString());
    assertEquals("∑{x0}([x1 = a0(x0)] * t0(x0))", uExprsRaw.targetExpr().toString());

    System.out.println("Rewritten UExpressions: ");
    final UExprTranslationResult uExprs =
        UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
    System.out.println("  [[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
    System.out.println("  [[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
    assertEquals("||∑{x0}(t0(x0) * [x1 = a0(x0)])||", uExprs.sourceExpr().toString());
    assertEquals("||∑{x0}(t0(x0) * [x1 = a0(x0)])||", uExprs.targetExpr().toString());
    final int result =
        LogicSupport.proveEq(uExprs, LogicSupport.PROVER_DISABLE_INTEGRITY_CONSTRAINTS_THEOREM);
    System.out.println("Prove result: " + LogicSupport.stringifyResult(result));
    assertEquals(LogicSupport.EQ, result, rule.toString());
  }

  @Test
  @Order(4)
  public void testUniqueSquashOnInSub() {
    /* Useful rule #24 */
    final Substitution rule =
        Substitution.parse(
            "Proj<a2 s1>(InSubFilter<a1>(Input<t0>,Proj<a0 s0>(Input<t1>)))|"
                + "Proj<a5 s2>(InnerJoin<a3 a4>(Input<t2>,Input<t3>))|"
                + "AttrsSub(a0,t1);AttrsSub(a1,t0);AttrsSub(a2,t0);"
                + "Unique(t1,a0);"
                + "TableEq(t2,t0);TableEq(t3,t1);AttrsEq(a3,a1);AttrsEq(a4,a0);AttrsEq(a5,a2);SchemaEq(s2,s1)");
    final UExprTranslationResult uExprsRaw = UExprSupport.translateToUExpr(rule);
    System.out.println("Raw UExpressions: ");
    System.out.println("  [[q0]](" + uExprsRaw.sourceOutVar() + ") := " + uExprsRaw.sourceExpr());
    System.out.println("  [[q1]](" + uExprsRaw.targetOutVar() + ") := " + uExprsRaw.targetExpr());
    assertEquals(
        "∑{x0,x1}([x2 = a2(x0)] * t0(x0) * [a1(x0) = a0(x1)] * not([IsNull(a0(x1))]) * t1(x1))",
        uExprsRaw.sourceExpr().toString());
    assertEquals(
        "∑{x0,x1}([x2 = a2(x0)] * t0(x0) * t1(x1) * [a1(x0) = a0(x1)] * not([IsNull(a0(x1))]))",
        uExprsRaw.targetExpr().toString());

    System.out.println("Rewritten UExpressions: ");
    final UExprTranslationResult uExprs =
        UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
    System.out.println("  [[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
    System.out.println("  [[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
    assertEquals(
        "∑{x0}([x2 = a2(x0)] * t0(x0) * ||∑{x1}(t1(x1) * [a1(x0) = a0(x1)] * not([IsNull(a0(x1))]))||)",
        uExprs.sourceExpr().toString());
    assertEquals(
        "∑{x0}([x2 = a2(x0)] * t0(x0) * ||∑{x1}(t1(x1) * [a1(x0) = a0(x1)] * not([IsNull(a0(x1))]))||)",
        uExprs.targetExpr().toString());
    final int result =
        LogicSupport.proveEq(uExprs, LogicSupport.PROVER_DISABLE_INTEGRITY_CONSTRAINTS_THEOREM);
    System.out.println("Prove result: " + LogicSupport.stringifyResult(result));
    assertEquals(LogicSupport.EQ, result, rule.toString());
  }

  @Test
  @Order(5)
  void testReferenceAndNotNull0() {
    /* Useful rule #6 */
    final Substitution rule =
        Substitution.parse(
            "LeftJoin<k0 k1>(Input<t0>,Input<t1>)|"
                + "InnerJoin<k2 k3>(Input<t2>,Input<t3>)|"
                + "AttrsSub(k0,t0);AttrsSub(k1,t1);"
                + "NotNull(t0,k0);Reference(t0,k0,t1,k1);"
                + "TableEq(t2,t0);TableEq(t3,t1);AttrsEq(k3,k1);AttrsEq(k2,k0)");
    final UExprTranslationResult uExprsRaw = UExprSupport.translateToUExpr(rule);
    System.out.println("Raw UExpressions: ");
    System.out.println("  [[q0]](" + uExprsRaw.sourceOutVar() + ") := " + uExprsRaw.sourceExpr());
    System.out.println("  [[q1]](" + uExprsRaw.targetOutVar() + ") := " + uExprsRaw.targetExpr());
    assertEquals(
        "t0(x0) * t1(x1) * [k0(x0) = k1(x1)] * not([IsNull(k1(x1))]) + t0(x0) * [IsNull(x1)] * not(∑{x2}(t1(x2) * [k0(x0) = k1(x2)] * not([IsNull(k1(x2))])))",
        uExprsRaw.sourceExpr().toString());
    assertEquals(
        "t0(x0) * t1(x1) * [k0(x0) = k1(x1)] * not([IsNull(k1(x1))])",
        uExprsRaw.targetExpr().toString());

    System.out.println("Rewritten UExpressions: ");
    final UExprTranslationResult uExprs =
        UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
    System.out.println("  [[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
    System.out.println("  [[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
    assertEquals("t0(x0) * t1(x1) * [k0(x0) = k1(x1)]", uExprs.sourceExpr().toString());
    assertEquals("t0(x0) * t1(x1) * [k0(x0) = k1(x1)]", uExprs.targetExpr().toString());
    final int result =
        LogicSupport.proveEq(uExprs, LogicSupport.PROVER_DISABLE_INTEGRITY_CONSTRAINTS_THEOREM);
    System.out.println("Prove result: " + LogicSupport.stringifyResult(result));
    assertEquals(LogicSupport.EQ, result, rule.toString());
  }

  @Test
  @Order(6)
  void testReferenceAndNotNull1() {
    /* Useful rule #7 (8) */
    final Substitution rule =
        Substitution.parse(
            "Proj<a2 s0>(InnerJoin<a0 a1>(Input<t0>,Input<t1>))|"
                + "Proj<a3 s1>(Input<t2>)|"
                + "AttrsSub(a0,t0);AttrsSub(a1,t1);AttrsSub(a2,t0);"
                + "NotNull(t0,a0);Reference(t0,a0,t1,a1);Unique(t1,a1);"
                + "TableEq(t2,t0);AttrsEq(a3,a2);SchemaEq(s1,s0)");
    final UExprTranslationResult uExprsRaw = UExprSupport.translateToUExpr(rule);
    System.out.println("Raw UExpressions: ");
    System.out.println("  [[q0]](" + uExprsRaw.sourceOutVar() + ") := " + uExprsRaw.sourceExpr());
    System.out.println("  [[q1]](" + uExprsRaw.targetOutVar() + ") := " + uExprsRaw.targetExpr());
    assertEquals(
        "∑{x0,x1}([x2 = a2(x0)] * t0(x0) * t1(x1) * [a0(x0) = a1(x1)] * not([IsNull(a1(x1))]))",
        uExprsRaw.sourceExpr().toString());
    assertEquals("∑{x0}([x2 = a2(x0)] * t0(x0))", uExprsRaw.targetExpr().toString());

    System.out.println("Rewritten UExpressions: ");
    final UExprTranslationResult uExprs =
        UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
    System.out.println("  [[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
    System.out.println("  [[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
    assertEquals("∑{x0}([x2 = a2(x0)] * t0(x0))", uExprs.sourceExpr().toString());
    assertEquals("∑{x0}([x2 = a2(x0)] * t0(x0))", uExprs.targetExpr().toString());
    final int result =
        LogicSupport.proveEq(uExprs, LogicSupport.PROVER_DISABLE_INTEGRITY_CONSTRAINTS_THEOREM);
    System.out.println("Prove result: " + LogicSupport.stringifyResult(result));
    assertEquals(LogicSupport.EQ, result, rule.toString());
  }

  @Test
  @Order(7)
  void testReferenceAndNotNullInsideSquash0() {
    final Substitution rule =
        Substitution.parse(
            "Proj*<a2 s0>(InnerJoin<a0 a1>(Input<t0>,Input<t1>))|"
                + "Proj*<a3 s1>(Input<t2>)|"
                + "AttrsSub(a0,t0);AttrsSub(a1,t1);AttrsSub(a2,t0);"
                + "NotNull(t0,a0);Reference(t0,a0,t1,a1);"
                + "TableEq(t2,t0);AttrsEq(a3,a2);SchemaEq(s1,s0)");
    final UExprTranslationResult uExprsRaw = UExprSupport.translateToUExpr(rule);
    System.out.println("Raw UExpressions: ");
    System.out.println("  [[q0]](" + uExprsRaw.sourceOutVar() + ") := " + uExprsRaw.sourceExpr());
    System.out.println("  [[q1]](" + uExprsRaw.targetOutVar() + ") := " + uExprsRaw.targetExpr());
    assertEquals(
        "||∑{x0,x1}([x2 = a2(x0)] * t0(x0) * t1(x1) * [a0(x0) = a1(x1)] * not([IsNull(a1(x1))]))||",
        uExprsRaw.sourceExpr().toString());
    assertEquals("||∑{x0}([x2 = a2(x0)] * t0(x0))||", uExprsRaw.targetExpr().toString());

    System.out.println("Rewritten UExpressions: ");
    final UExprTranslationResult uExprs =
        UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
    System.out.println("  [[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
    System.out.println("  [[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
    assertEquals("||∑{x0}([x2 = a2(x0)] * t0(x0))||", uExprs.sourceExpr().toString());
    assertEquals("||∑{x0}([x2 = a2(x0)] * t0(x0))||", uExprs.targetExpr().toString());
    final int result =
        LogicSupport.proveEq(uExprs, LogicSupport.PROVER_DISABLE_INTEGRITY_CONSTRAINTS_THEOREM);
    System.out.println("Prove result: " + LogicSupport.stringifyResult(result));
    assertEquals(LogicSupport.EQ, result, rule.toString());
  }

  @Test
  @Order(8)
  void testReferenceAndNotNullInsideSquash1() {
    /* Useful rule #15 */
    final Substitution rule =
        Substitution.parse(
            "InSub<k0>(Input<t0>,Proj<k1 s0>(Input<t1>))|"
                + "Input<t2>|"
                + "AttrsSub(k0,t0);AttrsSub(k1,t1);"
                + "NotNull(t0,k0);NotNull(t1,k1);TableEq(t0,t1);AttrsEq(k0,k1);TableEq(t2,t0)");
    final UExprTranslationResult uExprsRaw = UExprSupport.translateToUExpr(rule);
    System.out.println("Raw UExpressions: ");
    System.out.println("  [[q0]](" + uExprsRaw.sourceOutVar() + ") := " + uExprsRaw.sourceExpr());
    System.out.println("  [[q1]](" + uExprsRaw.targetOutVar() + ") := " + uExprsRaw.targetExpr());
    assertEquals(
        "t0(x0) * ||∑{x1}([k1(x0) = k1(x1)] * not([IsNull(k1(x1))]) * t0(x1))||",
        uExprsRaw.sourceExpr().toString());
    assertEquals("t0(x0)", uExprsRaw.targetExpr().toString());

    System.out.println("Rewritten UExpressions: ");
    final UExprTranslationResult uExprs =
        UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
    System.out.println("  [[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
    System.out.println("  [[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
    assertEquals("t0(x0) * ||∑{x1}([k1(x0) = k1(x1)] * t0(x1))||", uExprs.sourceExpr().toString());
    assertEquals("t0(x0)", uExprs.targetExpr().toString());
    final int result =
        LogicSupport.proveEq(uExprs, LogicSupport.PROVER_DISABLE_INTEGRITY_CONSTRAINTS_THEOREM);
    System.out.println("Prove result: " + LogicSupport.stringifyResult(result));
    assertEquals(LogicSupport.EQ, result, rule.toString());
  }

  @Test
  @Order(9)
  void testReferenceAndNotNullWithEqVarsTransform() {
    /* Useful rule #10 (9) */
    final Substitution rule =
        Substitution.parse(
            "Proj*<a3 s0>(Filter<p0 a2>(InnerJoin<a0 a1>(Input<t0>,Input<t1>)))|"
                + "Proj*<a5 s1>(Filter<p1 a4>(Input<t2>))|"
                + "AttrsEq(a1,a3);AttrsSub(a0,t0);AttrsSub(a1,t1);AttrsSub(a2,t0);AttrsSub(a3,t1);"
                + "NotNull(t0,a0);Reference(t0,a0,t1,a1);"
                + "TableEq(t2,t0);AttrsEq(a4,a2);AttrsEq(a5,a0);PredicateEq(p1,p0);SchemaEq(s1,s0)");
    final UExprTranslationResult uExprsRaw = UExprSupport.translateToUExpr(rule);
    System.out.println("Raw UExpressions: ");
    System.out.println("  [[q0]](" + uExprsRaw.sourceOutVar() + ") := " + uExprsRaw.sourceExpr());
    System.out.println("  [[q1]](" + uExprsRaw.targetOutVar() + ") := " + uExprsRaw.targetExpr());
    assertEquals(
        "||∑{x0,x1}([x2 = a1(x1)] * t0(x0) * t1(x1) * [a0(x0) = a1(x1)] * not([IsNull(a1(x1))]) * [p0(a2(x0))])||",
        uExprsRaw.sourceExpr().toString());
    assertEquals(
        "||∑{x0}([x2 = a0(x0)] * t0(x0) * [p0(a2(x0))])||", uExprsRaw.targetExpr().toString());

    System.out.println("Rewritten UExpressions: ");
    final UExprTranslationResult uExprs =
        UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
    System.out.println("  [[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
    System.out.println("  [[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
    assertEquals(
        "||∑{x0}([x2 = a0(x0)] * t0(x0) * [p0(a2(x0))])||", uExprs.sourceExpr().toString());
    assertEquals(
        "||∑{x0}([x2 = a0(x0)] * t0(x0) * [p0(a2(x0))])||", uExprs.targetExpr().toString());
    final int result =
        LogicSupport.proveEq(uExprs, LogicSupport.PROVER_DISABLE_INTEGRITY_CONSTRAINTS_THEOREM);
    System.out.println("Prove result: " + LogicSupport.stringifyResult(result));
    assertEquals(LogicSupport.EQ, result, rule.toString());
  }

  @Test
  @Order(10)
  void testUniqueSquashOnLeftJoinElimination() {
    /* Useful rule #11 (12) */
    final Substitution rule =
        Substitution.parse(
            "Proj<a2 s0>(LeftJoin<a0 a1>(Input<t0>,Input<t1>))|"
                + "Proj<a3 s1>(Input<t2>)|"
                + "AttrsSub(a0,t0);AttrsSub(a1,t1);AttrsSub(a2,t0);"
                + "Unique(t1,a1);TableEq(t2,t0);AttrsEq(a3,a2);SchemaEq(s1,s0)");
    final UExprTranslationResult uExprsRaw = UExprSupport.translateToUExpr(rule);
    System.out.println("Raw UExpressions: ");
    System.out.println("  [[q0]](" + uExprsRaw.sourceOutVar() + ") := " + uExprsRaw.sourceExpr());
    System.out.println("  [[q1]](" + uExprsRaw.targetOutVar() + ") := " + uExprsRaw.targetExpr());
    // Originally in WeTune, it is in the format of (WeTune can prove using Theorem 5.2):
    // [[q0]](x3) :=
    // ∑{x0,x1}(
    //   [x3 = a2(x0)] * t0(x0) * (
    //     t1(x1) * [a0(x0) = a1(x1)] * not([IsNull(a1(x1))]) +
    //     [IsNull(x1)] * not(∑{x2}(t1(x2) * [a0(x0) = a1(x2)] * not([IsNull(a1(x2))])))
    //   )
    // )
    // [[q1]](x3) := ∑{x0}([x3 = a2(x0)] * t0(x0))

    System.out.println("Rewritten UExpressions: ");
    final UExprTranslationResult uExprs =
        UExprSupport.translateToUExpr(rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
    System.out.println("  [[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
    System.out.println("  [[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
    // Now we normalize it into Normal Form (not supported by WeTune):
    // [[q0]](x3) :=
    //   ∑{x0}([x3 = a2(x0)] * t0(x0) * ||∑{x1}(t1(x1) * [a0(x0) = a1(x1)] *
    // not([IsNull(a1(x1))]))||) +
    //   ∑{x0,x1}([x3 = a2(x0)] * t0(x0) * [IsNull(x1)] * not(∑{x2}(t1(x2) * [a0(x0) = a1(x2)] *
    // not([IsNull(a1(x2))]))))
    // [[q1]](x3) := ∑{x0}([x3 = a2(x0)] * t0(x0))

    // Or I also tried the following form (also not supported by WeTune):
    // [[q0]](x3) :=
    //   ∑{x0}([x3 = a2(x0)] * t0(x0) * (
    //     ||∑{x1}(t1(x1) * [a0(x0) = a1(x1)] * not([IsNull(a1(x1))]))|| +
    //     ∑{x1}([IsNull(x1)] * not(∑{x2}(t1(x2) * [a0(x0) = a1(x2)] * not([IsNull(a1(x2))])))))
    //   )
    // [[q1]](x3) := ∑{x0}([x3 = a2(x0)] * t0(x0))
    // By using the following ad-hoc code...
    final UAdd add = (UAdd) uExprs.sourceExpr(); // \sum(body0) + \sum(body1)
    final UTerm body0 = ((USum) add.subTerms().get(0)).body();
    final List<UTerm> subTerms0 = body0.subTerms();
    final UTerm body1 = ((USum) add.subTerms().get(1)).body();
    final List<UTerm> subTerms1 = body1.subTerms();
    final Set<UVar> boundedVars0 = ((USum) add.subTerms().get(0)).boundedVars(); // x0
    final Set<UVar> boundedVars1 = ((USum) add.subTerms().get(1)).boundedVars(); // x0, x1
    boundedVars1.removeAll(boundedVars0);
    uExprs.srcExpr =
        USum.mk(
            boundedVars0,
            UMul.mk(
                subTerms0.get(0),
                subTerms0.get(1),
                UAdd.mk(
                    subTerms0.get(2),
                    USum.mk(boundedVars1, UMul.mk(subTerms1.subList(2, subTerms1.size()))))));
    System.out.println("  [[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
    System.out.println("  [[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
    final int result =
        LogicSupport.proveEq(uExprs, LogicSupport.PROVER_DISABLE_INTEGRITY_CONSTRAINTS_THEOREM);
    // It contains Latent Summation (Sum(..Sum)), and cannot be turned it into the supported form:
    // ∑{x0,x1}(..)=∑{x0}(..), but it can be manually proved EQ based on the expression.
    // Maybe SQLSolver can solve it.
    System.out.println("Prove result: " + LogicSupport.stringifyResult(result));
  }

  @Test
  void checkRulesWithIC() throws IOException {
    final Path ruleFilePath = dataDir().resolve("prepared").resolve("rules.txt");
    final SubstitutionBank rules = SubstitutionSupport.loadBank(ruleFilePath);
    int count = 0, errs = 0;
    final Map<Integer, List<Integer>> stats = new HashMap<>(); // result -> #
    final List<Integer> errIds = new ArrayList<>();
    // int targetId = 177;
    for (Substitution rule : rules.rules()) {
      // if (rule.id() != targetId) continue;
      if (any(rule.constraints(), c -> c.kind().isIntegrityConstraint())) {
        ++count;
        try {
          final UExprTranslationResult uExprsRaw = UExprSupport.translateToUExpr(rule);
          // final int resultRaw =
          //     LogicSupport.proveEq(uExprsRaw);
          System.out.println("Rule id: " + rule.id());
          // System.out.println(
          //     "Raw of Rule id: " + rule.id() + " is " + LogicSupport.stringifyResult(resultRaw));
          System.out.println("Raw UExpressions: ");
          System.out.println(
              "  [[q0]](" + uExprsRaw.sourceOutVar() + ") := " + uExprsRaw.sourceExpr());
          System.out.println(
              "  [[q1]](" + uExprsRaw.targetOutVar() + ") := " + uExprsRaw.targetExpr());

          final UExprTranslationResult uExprs =
              UExprSupport.translateToUExpr(
                  rule, UExprSupport.UEXPR_FLAG_INTEGRITY_CONSTRAINT_REWRITE);
          final int result =
              LogicSupport.proveEq(
                  uExprs, LogicSupport.PROVER_DISABLE_INTEGRITY_CONSTRAINTS_THEOREM);
          System.out.println(
              "Rule id: " + rule.id() + " is " + LogicSupport.stringifyResult(result));
          System.out.println("Rewritten UExpressions: ");
          System.out.println("  [[q0]](" + uExprs.sourceOutVar() + ") := " + uExprs.sourceExpr());
          System.out.println("  [[q1]](" + uExprs.targetOutVar() + ") := " + uExprs.targetExpr());
          stats.computeIfAbsent(result, r -> new ArrayList<>()).add(rule.id());
          // assertEquals(LogicSupport.EQ, result, rule.toString());
        } catch (Error e) {
          errIds.add(rule.id());
          ++errs;
        }
      }
    }
    System.out.printf("Totally have %d rules with IC%n", count);
    System.out.printf("Errors: %d%n", errs);
    for (var pairs : stats.entrySet()) {
      System.out.println(
          LogicSupport.stringifyResult(pairs.getKey())
              + "(" + (stats.get(pairs.getKey()).size())
              + "): "
              + stats.get(pairs.getKey()));
    }
    System.out.println("Errs" + ": " + errIds);
  }
}

package wtune.superopt.lia;

import org.junit.jupiter.api.Test;
import wtune.common.utils.IOSupport;
import wtune.common.utils.Lazy;
import wtune.sql.ast.ExprFields;
import wtune.sql.ast.SqlNode;
import wtune.sql.ast.constants.JoinKind;
import wtune.sql.plan.*;
import wtune.sql.schema.Schema;
import wtune.stmt.Statement;
import wtune.superopt.fragment.SetOp;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.*;

import static wtune.common.utils.ListSupport.filter;
import static wtune.sql.ast.ExprKind.Aggregate;
import static wtune.sql.ast.ExprKind.Binary;
import static wtune.sql.plan.PlanSupport.assemblePlan;
import static wtune.sql.support.action.NormalizationSupport.normalizeAst;
import static wtune.superopt.TestHelper.dataDir;

public class PlanOperatorStatistic {
  @Test
  void operatorStatistic() throws IOException {
    final Path res = dataDir().resolve("lia").resolve("opStatistics_"
        + LocalDateTime.now().format(DateTimeFormatter.ofPattern("MMddHHmmss"))
        + ".csv");
    if (!Files.exists(res)) {
      Files.createDirectories(res.getParent());
      Files.createFile(res);
    }

    final Set<String> failures = new HashSet<>();
    final Map<String, Set<String>> stmtStatistics = new HashMap<>();
    final List<Statement> stmts = Statement.findAll();
    for (Statement stmt : stmts) {
      final PlanContext plan = parsePlan(stmt);
      if (plan == null) {
        failures.add(stmt.toString());
        continue;
      }
      stmtStatistics.put(stmt.toString(), new HashSet<>());
      final Set<String> thisStatistics = stmtStatistics.get(stmt.toString());
      traverseTree(plan.root(), plan, thisStatistics);
    }
    System.out.println("failures: " + failures.size());

    final Set<String> allOpNames = new HashSet<>();
    for (String key : stmtStatistics.keySet()) {
      allOpNames.addAll(stmtStatistics.get(key));
    }
    final List<String> allOpNameList = allOpNames.stream().sorted().toList();

    final StringBuilder head = new StringBuilder("stmtId");
    for (String opName : allOpNameList) {
      head.append(",").append(opName);
    }
    IOSupport.appendTo(res, out -> out.printf(head.toString() + "\n"));

    for (String stmtId : stmtStatistics.keySet()) {
      final Set<String> stat = stmtStatistics.get(stmtId);
      final StringBuilder sb = new StringBuilder(stmtId);
      for (String opName : allOpNameList) {
        sb.append(",").append(stat.contains(opName) ? 1 : 0);
      }
      IOSupport.appendTo(res, out -> out.printf(sb.toString() + "\n"));
      // System.out.println(stmtStatistics.get(stmts.get(i).toString()));
    }

  }

  private void traverseTree(int nodeId, PlanContext ctx, Set<String> statistics) {
    final PlanNode node = ctx.nodeAt(nodeId);
    if (node.numChildren(ctx) > 0) traverseTree(ctx.childOf(nodeId, 0), ctx, statistics);
    if (node.numChildren(ctx) > 1) traverseTree(ctx.childOf(nodeId, 1), ctx, statistics);

    switch (ctx.kindOf(nodeId)) {
      case Input, InSub, Exists, Proj, Sort, Limit -> {
        final String key = ctx.kindOf(nodeId).name();
        statistics.add(key);
      }
      case SetOp -> {
        final String key = ((SetOpNode) node).opKind().name();
        statistics.add(key);
      }
      case Join -> {
        final JoinKind joinKind = ((JoinNode) node).joinKind();
        final String key = "Join_" + (joinKind.isInner() ? "Inner" : "Outer");
        statistics.add(key);
      }
      case Agg -> {
        final List<Expression> aggExprs =
            filter(((AggNode) node).attrExprs(), e -> Aggregate.isInstance(e.template()));
        final Set<String> aggFuncNames = new HashSet<>();
        for (Expression e : aggExprs) {
          aggFuncNames.add(e.template().$(ExprFields.Aggregate_Name));
        }
        for (String aggFunc : aggFuncNames) {
          final String key = "Agg_" + aggFunc;
          statistics.add(key);
        }
      }
      case Filter -> {
        final Expression predicate = ((SimpleFilterNode) node).predicate();
        if (Binary.isInstance(predicate.template())) {
          switch (predicate.template().$(ExprFields.Binary_Op)) {
            case EQUAL -> statistics.add("Filter_EQ");
            case NOT_EQUAL, LESS_THAN, LESS_OR_EQUAL, GREATER_THAN, GREATER_OR_EQUAL -> statistics.add("Filter_NEQ");
            case OR -> statistics.add("Filter_OR");
            default -> statistics.add("Filter_OTHER");
          }
        } else statistics.add("Filter_OTHER");
      }
    }
  }

  private PlanContext parsePlan(Statement stmt) {
    final Schema schema = stmt.app().schema("base", true);
    try {
      final SqlNode ast = stmt.ast();
      if (ast == null) return null;

      if (!PlanSupport.isSupported(ast)) {
        // System.err.println("fail to parse plan " + stmt + " due to unsupported SQL feature");
        return null;
      }
      ast.context().setSchema(schema);
      normalizeAst(ast);

      final PlanContext plan = assemblePlan(ast, schema);
      // if (plan == null)
        // System.err.println("fail to parse plan " + stmt + " due to " + PlanSupport.getLastError());

      return plan;
    } catch (Throwable ex) {
      // System.err.println("fail to parse sql/plan " + stmt + " due to exception");
      ex.printStackTrace();
    }
    return null;
  }
}

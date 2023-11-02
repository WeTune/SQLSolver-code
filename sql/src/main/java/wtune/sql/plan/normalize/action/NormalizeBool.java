package wtune.sql.plan.normalize.action;

import wtune.common.utils.ListSupport;
import wtune.sql.ast.ExprFields;
import wtune.sql.ast.ExprKind;
import wtune.sql.ast.SqlDataType;
import wtune.sql.ast.SqlNode;
import wtune.sql.ast.constants.LiteralKind;
import wtune.sql.plan.PlanSupport;
import wtune.sql.ast.constants.BinaryOpKind;
import wtune.sql.plan.Expression;
import wtune.sql.plan.PlanContext;
import wtune.sql.plan.SimpleFilterNode;
import wtune.sql.plan.Value;
import wtune.sql.schema.Column;

import java.util.List;

import static wtune.sql.ast.SqlNodeFields.Expr_Kind;
import static wtune.sql.util.TypeConverter.isConvertibleStringToInt;

public class NormalizeBool {

  public static void normalizeFilter(int nodeId, PlanContext plan) {
    SimpleFilterNode filter = (SimpleFilterNode) plan.nodeAt(nodeId);
    final Expression predExpr = filter.predicate();
    final SqlNode predNode = predExpr.template();

    ExprKind exprKind = predNode.$(Expr_Kind);
    switch (exprKind)  {
      case Binary -> {
        final BinaryOpKind binaryOpKind = predNode.$(ExprFields.Binary_Op);
        final SqlNode lhs = predNode.$(ExprFields.Binary_Left);
        final SqlNode rhs = predNode.$(ExprFields.Binary_Right);
        if (binaryOpKind.isComparison()) {
          /* for comparison filter,  a {=,<>,<,>,<=,>=} CONST, when a's type is different from CONST => FALSE
          e.g a = 'test' and a's type is INTEGER => FALSE
          */

          final SqlNode cstNode = ExprKind.Literal.isInstance(rhs) ? rhs : ExprKind.Literal.isInstance(lhs) ? lhs : null;
          final SqlNode refNode = ExprKind.ColRef.isInstance(rhs) ? rhs : ExprKind.ColRef.isInstance(lhs) ? lhs : null;

          if (cstNode != null && refNode != null) {
            if (cstNode.$(ExprFields.Literal_Kind) == LiteralKind.NULL) break;
            final int index = predExpr.internalRefs().indexOf(refNode);
            if (index < 0) break;
            final Value param = plan.valuesReg().valueRefsOf(predExpr).get(index);
            final Column refColumn = PlanSupport.tryResolveColumn(plan, param);
            if (refColumn != null)
              switch (refColumn.dataType().category()) {
                case INTEGRAL -> {
                  if (cstNode.$(ExprFields.Literal_Kind) != LiteralKind.INTEGER
                          && !isConvertibleStringToInt((String)cstNode.$(ExprFields.Literal_Value))) {
                    replaceFilterWithFalse(cstNode, filter, plan);
                  }
                }
                default -> {}
              }
          }
        }
      }
    }
  }

  private static void replaceFilterWithFalse(SqlNode cstNode, SimpleFilterNode filter, PlanContext plan) {
    final SqlNode literal = SqlNode.mk(cstNode.context(), ExprKind.Literal);
    literal.$(ExprFields.Literal_Kind, LiteralKind.BOOL);
    literal.$(ExprFields.Literal_Value, false);
    filter.setPredicate(Expression.mk(literal));
    PlanSupport.resolvePlan(plan);
  }
}

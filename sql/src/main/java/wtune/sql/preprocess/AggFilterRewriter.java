package wtune.sql.preprocess;

import org.apache.calcite.sql.*;
import org.apache.calcite.sql.fun.SqlCase;
import org.apache.calcite.sql.parser.SqlParserPos;

// agg(expr) FILTER(WHERE pred)
// ->
// agg(CASE WHEN pred THEN expr ELSE NULL END)
public class AggFilterRewriter extends SqlNodePreprocess {

  // CASE WHEN pred THEN expr ELSE NULL END
  private SqlCase caseWhenElseNull(SqlNode pred, SqlNode expr) {
    SqlNodeList whenList = SqlNodeList.of(pred);
    SqlNodeList thenList = SqlNodeList.of(expr);
    SqlNode elseExpr = SqlLiteral.createNull(SqlParserPos.ZERO);
    return new SqlCase(SqlParserPos.ZERO, null, whenList, thenList, elseExpr);
  }

  @Override
  public SqlNode preprocess(SqlNode node) {
    if (node instanceof SqlSelect select) {
      SqlNodeList newSelectList = new SqlNodeList(SqlParserPos.ZERO);
      for (SqlNode expr : select.getSelectList()) {
        newSelectList.add(handleFilter(expr));
      }
      select.setSelectList(newSelectList);
      // recursion is not implemented yet
    }
    return node;
  }

  private SqlNode handleFilter(SqlNode expr) {
    if (expr instanceof SqlBasicCall call) {
      if (call.getOperator() instanceof SqlFilterOperator
            && call.operand(0) instanceof SqlBasicCall agg
            && agg.getOperator() instanceof SqlAggFunction
            && agg.operandCount() == 1) {
        SqlCase caseWhen = caseWhenElseNull(call.operand(1), agg.operand(0));
        SqlBasicCall newAgg = (SqlBasicCall) agg.clone(SqlParserPos.ZERO);
        newAgg.setOperand(0, caseWhen);
        return newAgg;
      } else {
        // recursion
        for (int i = 0; i < call.operandCount(); i++) {
          call.setOperand(i, handleFilter(call.operand(i)));
        }
      }
    }
    return expr;
  }

}

package wtune.sql.preprocess;

import org.apache.calcite.sql.*;
import org.apache.calcite.sql.parser.SqlParserPos;

import java.math.BigDecimal;
import java.math.RoundingMode;

public class NumericConstantRewriter extends RecursiveRewriter {
  @Override
  public SqlNode handleNode(SqlNode node) {
    if (node instanceof SqlBasicCall call) {
      SqlOperator op = call.getOperator();
      switch (op.getKind()) {
        case PLUS -> {
          SqlNode left = call.operand(0), right = call.operand(1);
          left = handleNode(left);
          right = handleNode(right);
          if (left instanceof SqlNumericLiteral l1
                  && right instanceof SqlNumericLiteral l2) {
            BigDecimal result = l1.bigDecimalValue().add(l2.bigDecimalValue());
            return SqlLiteral.createExactNumeric(result.toString(), SqlParserPos.ZERO);
          }
        }
        case MINUS -> {
          SqlNode left = call.operand(0), right = call.operand(1);
          left = handleNode(left);
          right = handleNode(right);
          if (left instanceof SqlNumericLiteral l1
                  && right instanceof SqlNumericLiteral l2) {
            BigDecimal result = l1.bigDecimalValue().subtract(l2.bigDecimalValue());
            return SqlLiteral.createExactNumeric(result.toString(), SqlParserPos.ZERO);
          }
        }
      }
    } else if (node instanceof SqlNumericLiteral literal) {
      BigDecimal decimal = literal.bigDecimalValue();
      if (decimal.scale() > 0) {
        // truncate the fractional part
        BigDecimal round = decimal.setScale(0, RoundingMode.FLOOR)
                .setScale(decimal.scale());
        if (decimal.equals(round)) {
          round = decimal.setScale(0, RoundingMode.FLOOR);
          return SqlLiteral.createExactNumeric(round.toString(), SqlParserPos.ZERO);
        }
      }
    }
    return node;
  }
}

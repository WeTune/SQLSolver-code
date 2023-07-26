package wtune.sql.preprocess;

import org.apache.calcite.sql.*;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.sql.parser.SqlParserPos;
import org.apache.calcite.sql.type.OperandTypes;
import org.apache.calcite.sql.type.ReturnTypes;
import org.apache.calcite.sql.validate.SqlMonotonicity;

import java.util.Collections;

// a LIKE b -> a - b = LIKE_STRING -> uninterpreted function
public class LikeRewriter extends RecursiveRewriter {

  public static final String LIKE_STRING = "LIKE_OP";

  public static class LikeOpFunction extends SqlFunction {
    public LikeOpFunction() {
      super(LIKE_STRING, SqlKind.OTHER_FUNCTION,
              ReturnTypes.BOOLEAN, null, OperandTypes.STRING_SAME_SAME,
              SqlFunctionCategory.SYSTEM);
    }

    @Override
    public SqlSyntax getSyntax() {
      return SqlSyntax.FUNCTION;
    }

    @Override
    public String getSignatureTemplate(int operandCount) {
      return "{0}(<arg1>, <arg2>)";
    }

    @Override
    public SqlCall createCall(SqlLiteral functionQualifier, SqlParserPos pos, SqlNode... operands) {
      return new SqlBasicCall(this, operands, pos);
    }

    @Override
    public SqlMonotonicity getMonotonicity(SqlOperatorBinding call) {
      return SqlMonotonicity.CONSTANT;
    }
  }

  @Override
  public boolean prepare(SqlNode node) {
    return !node.toString().contains(LIKE_STRING);
  }

  @Override
  public SqlNode handleNode(SqlNode node) {
    if (node instanceof SqlBasicCall call) {
      SqlOperator op = call.getOperator();
      if (op.getKind().equals(SqlKind.LIKE)) {
        SqlNode like = (new LikeOpFunction()).createCall(SqlParserPos.ZERO,
                call.operand(0), call.operand(1));
        SqlNode zero = SqlLiteral.createExactNumeric("0", SqlParserPos.ZERO);
        boolean not = op.equals(SqlStdOperatorTable.NOT_LIKE);
        // like_op returns non-zero upon match, or 0 otherwise
        if (not) {
          return SqlStdOperatorTable.EQUALS.createCall(SqlParserPos.ZERO,
                  like, zero);
        } else {
          return SqlStdOperatorTable.NOT_EQUALS.createCall(SqlParserPos.ZERO,
                  like, zero);
        }
      }
    }
    return node;
  }

}

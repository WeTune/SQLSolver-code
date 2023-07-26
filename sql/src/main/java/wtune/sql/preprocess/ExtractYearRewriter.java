package wtune.sql.preprocess;

import org.apache.calcite.sql.*;
import org.apache.calcite.sql.fun.SqlExtractFunction;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.sql.parser.SqlParserPos;

import java.util.Collections;

public class ExtractYearRewriter extends RecursiveRewriter {

  @Override
  public SqlNode handleNode(SqlNode node) {
    if (node instanceof SqlBasicCall call
            && call.getOperator() instanceof SqlExtractFunction
            && call.operand(0).toString().equalsIgnoreCase("YEAR")) {
      return SqlStdOperatorTable.YEAR.createCall(SqlParserPos.ZERO,
                Collections.singletonList(call.operand(1)));
    }
    return node;
  }

}

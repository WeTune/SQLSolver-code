package wtune.sql.preprocess;

import org.apache.calcite.sql.*;
import org.apache.calcite.sql.parser.SqlParserPos;
import org.apache.calcite.util.DateString;

import java.text.DateFormat;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.Date;
import java.util.GregorianCalendar;

public class DateOpRewriter extends RecursiveRewriter {

  private String dateAdd(String dateStr, int field, int amount) {
    DateFormat format = new SimpleDateFormat("yyyy-MM-dd");
    try {
      Date date = format.parse(dateStr);
      Calendar calendar = new GregorianCalendar();
      calendar.setTime(date);
      calendar.add(field, amount);
      Date newDate = calendar.getTime();
      return format.format(newDate);
    } catch (ParseException e) {
      assert false;
    }
    return null;
  }

  private SqlDateLiteral dateAdd(SqlDateLiteral dateNode, SqlIntervalLiteral intNode) {
    String dateStr = dateNode.getValue().toString();
    int field = -1;
    switch (intNode.getTypeName()) {
      case INTERVAL_DAY -> field = Calendar.DAY_OF_MONTH;
      case INTERVAL_MONTH -> field = Calendar.MONTH;
      case INTERVAL_YEAR -> field = Calendar.YEAR;
      default -> {
        assert false; // unsupported
      }
    }
    int amount = Integer.parseInt(intNode.getValue().toString());
    String newDateStr = dateAdd(dateStr, field, amount);
    return SqlLiteral.createDate(new DateString(newDateStr), SqlParserPos.ZERO);
  }

  // calculate data_sub and fold it into a date constant
  private SqlDateLiteral foldDateSub(SqlCall dateSub) {
    String dateStr = ((SqlCharStringLiteral) dateSub.operand(0)).getNlsString().getValue();
    int amount = -((SqlNumericLiteral) dateSub.operand(1)).intValue(true);
    String newDateStr = dateAdd(dateStr, Calendar.DAY_OF_MONTH, amount);
    return SqlLiteral.createDate(new DateString(newDateStr), SqlParserPos.ZERO);
  }

  @Override
  public SqlNode handleNode(SqlNode node) {
    if (node instanceof SqlBasicCall call) {
      SqlOperator op = call.getOperator();
      if (op instanceof SqlUnresolvedFunction funcOp) {
        switch (funcOp.getName()) {
          case "DATE_SUB" -> {
            return foldDateSub(call);
          }
        }
      } else if (op.getKind().equals(SqlKind.PLUS)) {
        if (call.operand(0) instanceof SqlDateLiteral dateNode
                && call.operand(1) instanceof SqlIntervalLiteral intNode) {
          // date 'yyyy-MM-dd' + interval ...
          return dateAdd(dateNode, intNode);
        }
      }
    }
    return node;
  }

}

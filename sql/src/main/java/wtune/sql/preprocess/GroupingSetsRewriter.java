package wtune.sql.preprocess;

import org.apache.calcite.sql.*;
import org.apache.calcite.sql.fun.SqlRowOperator;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.sql.parser.SqlParserPos;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

//  SELECT
//    DEPTNO, ENAME, JOB,
//    GROUPING(DEPTNO, ENAME, JOB) = 1 AS $g_1,
//    GROUPING(DEPTNO, ENAME, JOB) = 2 AS $g_2
//  FROM
//    EMP
//  GROUP BY
//    GROUPING SETS(
//      (ENAME, DEPTNO),
//      (JOB, DEPTNO)
//    )
//
//  ->
//
//  SELECT
//    DEPTNO, ENAME, NULL AS JOB,
//    1 = 1 AS $g_1,
//    1 = 2 AS $g_2
//  FROM
//    EMP
//  GROUP BY
//    ENAME, DEPTNO
//  UNION ALL
//  SELECT
//    DEPTNO, NULL AS ENAME, JOB,
//    2 = 1 AS $g_1,
//    2 = 2 AS $g_2
//  FROM
//    EMP
//  GROUP BY
//    JOB, DEPTNO
public class GroupingSetsRewriter extends SqlNodePreprocess {

  private static final int GROUP_GROUPING_SETS = 1;
  private static final int GROUP_SIMPLE = 2;
  private static final int GROUP_UNSUPPORT = -1;

  private SqlIdentifier id(String name) {
    return new SqlIdentifier(name, SqlParserPos.ZERO);
  }

  private SqlBasicCall as(SqlNode node, SqlNode alias) {
    return new SqlBasicCall(new SqlAsOperator(), new SqlNode[]{node, alias}, SqlParserPos.ZERO);
  }

  private boolean isDesiredPattern(SqlSelect select) {
    SqlNode from = select.getFrom();
    SqlNodeList group = select.getGroup();
    return !(from == null || group == null
            || select.getHaving() != null
            || select.getWindowList().size() > 0
            || select.getOrderList() != null
            || select.getOffset() != null
            || select.getFetch() != null);
  }

  private int groupType(SqlNodeList group) {
    SqlNode[] groupList = null;
    int result = GROUP_UNSUPPORT;
    // unwrap single GROUPING SETS
    if (group.get(0) instanceof SqlBasicCall gsets) {
      if (group.size() == 1
              && gsets.getOperator().equals(SqlStdOperatorTable.GROUPING_SETS)
              && gsets.operandCount() > 0) {
        // single "GROUPING SETS" which contains at least one operand
        groupList = gsets.operands;
        result = GROUP_GROUPING_SETS;
      }
    } else {
      // simple group list
      groupList = group.toArray();
      result = GROUP_SIMPLE;
    }
    // check whether <groupList> (with GROUPING SETS unwrapped, or raw) only contains columns
    if (groupList != null) {
      for (SqlNode operand : groupList) {
        if (operand instanceof SqlBasicCall row
                && row.getOperator() instanceof SqlRowOperator) {
          for (SqlNode ele : row.operands) {
            if (!(ele instanceof SqlIdentifier)) return GROUP_UNSUPPORT;
          }
        } else if (!(operand instanceof SqlIdentifier
                || (operand instanceof SqlNodeList list && list.size() == 0))) {
          return GROUP_UNSUPPORT;
        }
      }
      return result;
    }
    return GROUP_UNSUPPORT;
  }

  private boolean containsGrouping(SqlNode node) {
    if (node instanceof SqlBasicCall call) {
      if (call.getOperator().equals(SqlStdOperatorTable.GROUPING))
        return true;
      for (SqlNode child : call.operands) {
        if (containsGrouping(child)) return true;
      }
    }
    return false;
  }

  private boolean containsGrouping(SqlNodeList list) {
    for (SqlNode node : list) {
      if (containsGrouping(node)) return true;
    }
    return false;
  }

  private boolean hasEmptyGroupingSet(SqlNode[] gsets) {
    for (SqlNode gset : gsets) {
      if (gset instanceof SqlNodeList list && list.size() == 0) {
        return true;
      }
    }
    return false;
  }

  private boolean containsAgg(SqlNodeList list) {
    for (SqlNode node : list) {
      if (node instanceof SqlBasicCall call
              && call.getOperator() instanceof SqlAggFunction) {
        return true;
      }
    }
    return false;
  }

  // SELECT agg() ... GROUP BY GROUPING SETS (... () ...)
  // ->
  // SELECT agg() ...
  //
  // But "SELECT 1 FROM ... GROUP BY GROUPING SETS (... () ...)"
  // != "SELECT 1 FROM ..."
  private boolean emptyGroupingSetHasAgg(SqlSelect select) {
    SqlNodeList group = select.getGroup();
    assert group.size() == 1 && group.get(0) instanceof SqlBasicCall;
    SqlBasicCall gsets = (SqlBasicCall) group.get(0);
    // no empty grouping set, the predicate is trivially true
    if (!hasEmptyGroupingSet(gsets.operands)) return true;
    // with empty grouping set, select list should contain agg
    return containsAgg(select.getSelectList());
  }

  // 0. <select> should be "SELECT ... FROM ... GROUP BY ..."
  // 1. GROUP BY should be a "GROUPING SETS" or a list of columns and only contain columns
  private boolean needsHandle(SqlSelect select) {
    SqlNodeList group = select.getGroup();
    return isDesiredPattern(select)
            && groupType(group) != GROUP_UNSUPPORT
            && (groupType(group) != GROUP_SIMPLE || containsGrouping(select.getSelectList()))
            && (groupType(group) != GROUP_GROUPING_SETS || emptyGroupingSetHasAgg(select));
  }

  @Override
  public SqlNode preprocess(SqlNode node) {
    if (node instanceof SqlSelect select) {
      // check if node needs to be handled
      if (needsHandle(select)) {
        // generate a subquery for each grouping set
        List<SqlNode> queries = queriesFromGroupingSets(select);
        // return UNION ALL of generated subqueries
        return unionAll(queries);
      } else {
        // recursion
        select.setFrom(preprocess(select.getFrom()));
      }
    } else if (node instanceof SqlBasicCall call) {
      // recursion
      for (int i = 0; i < call.operands.length; i++) {
        SqlNode child = call.operand(i);
        SqlNode childNew = preprocess(child);
        if (childNew != child) {
          call.setOperand(i, childNew);
        }
      }
    }
    return node;
  }

  // generate a query for each grouping set
  private List<SqlNode> queriesFromGroupingSets(SqlSelect select) {
    // find grouping sets & group columns
    SqlNodeList group = select.getGroup();
    List<Set<String>> groupingSets = new ArrayList<>();
    Set<String> groupColumns = new HashSet<>();
    if (group.get(0) instanceof SqlBasicCall gsets) {
      // single GROUPING SETS
      for (SqlNode operand : gsets.operands) {
        // for each grouping set (a row or an identifier)
        Set<String> groupingSet = new HashSet<>();
        if (operand instanceof SqlBasicCall row) {
          for (SqlNode column : row.operands) {
            groupingSet.add(column.toString());
            groupColumns.add(column.toString());
          }
        } else if (operand instanceof SqlIdentifier id) {
          groupingSet.add(id.toString());
          groupColumns.add(id.toString());
        }
        groupingSets.add(groupingSet);
      }
    } else {
      // simple group list
      Set<String> groupingSet = new HashSet<>();
      for (SqlNode column : group) {
        groupingSet.add(column.toString());
        groupColumns.add(column.toString());
      }
      groupingSets.add(groupingSet);
    }
    // generate queries for grouping sets
    List<SqlNode> queries = new ArrayList<>();
    SqlNodeList list = select.getSelectList();
    SqlNode from = select.getFrom();
    for (Set<String> groupingSet : groupingSets) {
      queries.add(queryFromGroupingSet(list, from, groupingSet, groupColumns));
    }
    return queries;
  }

  // generate a query for a grouping set
  private SqlNode queryFromGroupingSet(SqlNodeList selectList, SqlNode from, Set<String> groupingSet, Set<String> groupColumns) {
    // construct the new SELECT list
    SqlNodeList newSelectList = new SqlNodeList(SqlParserPos.ZERO);
    for (SqlNode item : selectList) {
      newSelectList.add(convertSelectItem(item, groupingSet, groupColumns));
    }
    // GROUP BY
    SqlNodeList group = new SqlNodeList(SqlParserPos.ZERO);
    for (String column : groupingSet) {
      group.add(id(column));
    }
    if (group.size() == 0) group = null;
    // return
    return new SqlSelect(SqlParserPos.ZERO, new SqlNodeList(SqlParserPos.ZERO),
            newSelectList, from.clone(SqlParserPos.ZERO), null, group,
            null, new SqlNodeList(SqlParserPos.ZERO), null, null, null);
  }

  // wrapper which adds a necessary alias
  // grouping column "C" -> "NULL AS C" if C is not in the grouping set but in group columns
  private SqlNode convertSelectItem(SqlNode item, Set<String> groupingSet, Set<String> groupColumns) {
    SqlNode alias = null, newItem = item;
    if (item instanceof SqlBasicCall call
            && call.getOperator() instanceof SqlAsOperator) {
      newItem = call.operand(0);
      alias = call.operand(1);
    } else if (item instanceof SqlIdentifier) {
      // column name itself as an alias
      alias = item;
    }
    newItem = convertNode(newItem, groupingSet, groupColumns);
    if (newItem == item) return item;
    if (alias != null) newItem = as(newItem, alias);
    return newItem;
  }

  // recursive
  // grouping column "C" -> "NULL" if C is not in the grouping set but in group columns
  // GROUPING(...) -> a constant
  private SqlNode convertNode(SqlNode node, Set<String> groupingSet, Set<String> groupColumns) {
    if (node instanceof SqlBasicCall call) {
      if (call.getOperator().equals(SqlStdOperatorTable.GROUPING)) {
        // calculate GROUPING
        int value = 0, mask = 1 << (call.operandCount() - 1);
        for (SqlNode arg : call.operands) {
          if (!groupingSet.contains(arg.toString())) value |= mask;
          mask >>= 1;
        }
        return SqlNumericLiteral.createExactNumeric(String.valueOf(value), SqlParserPos.ZERO);
      } else {
        // recursion
        boolean updated = false;
        SqlNode[] newOperands = new SqlNode[call.operandCount()];
        for (int i = 0; i < call.operandCount(); i++) {
          SqlNode child = call.operand(i);
          SqlNode newChild = convertNode(child, groupingSet, groupColumns);
          newOperands[i] = newChild;
          if (child != newChild) {
            updated = true;
          }
        }
        if (updated) {
          return call.getOperator().createCall(SqlParserPos.ZERO, newOperands);
        }
      }
    } else if (node instanceof SqlIdentifier id) {
      String column = id.toString();
      if (!groupingSet.contains(column) && groupColumns.contains(column)) {
        // C -> NULL
        return SqlLiteral.createNull(SqlParserPos.ZERO);
      }
    }
    return node;
  }

  // q1 UNION ALL q2 UNION ALL ...
  private SqlNode unionAll(List<SqlNode> nodes) {
    SqlNode union = nodes.get(0);
    for (int i = 1; i < nodes.size(); i++) {
      union = SqlStdOperatorTable.UNION_ALL.createCall(SqlParserPos.ZERO,
              union, nodes.get(i));
    }
    return union;
  }
}

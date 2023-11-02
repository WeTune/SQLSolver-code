package wtune.sql;

import org.antlr.v4.runtime.misc.ParseCancellationException;
import wtune.common.field.FieldKey;
import wtune.common.tree.LabeledTreeFields;
import wtune.sql.ast.constants.*;
import wtune.sql.parser.AstParser;
import wtune.sql.preprocess.CastHandler;
import wtune.sql.preprocess.SemiAntiJoinHandler;
import wtune.sql.copreprocess.SqlNodeCoPreprocess;
import wtune.sql.preprocess.SqlNodePreprocess;
import wtune.sql.util.SqlCopier;
import wtune.sql.ast.*;
//import

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static wtune.common.datasource.DbSupport.*;
import static wtune.common.tree.TreeSupport.nodeEquals;
import static wtune.common.utils.Commons.unquoted;
import static wtune.sql.ast.constants.BinaryOpKind.*;

public abstract class SqlSupport {
  private static boolean PARSING_ERROR_MUTED = false;

  private SqlSupport() {}

  public static void muteParsingError() {
    PARSING_ERROR_MUTED = true;
  }

  public static int coalesceEndIndex(int startIndex, String query) {
    int counter = 1;
    for (int i = startIndex + 1; i < query.length(); ++ i) {
      if (query.charAt(i) == '(')
        counter ++;
      else if (query.charAt(i) == ')')
        counter --;
      if (counter == 0)
        return i;
    }
    assert false;
    return 0;
  }

  private static String aggNullToZero(String[] params) {
    if(params.length == 2 && params[1].equals("0") && params[0].indexOf("(")!=0)
      return params[0];
    else
      return null;
  }


  public static String coalesceHandler(String query, int coalesceBegin) {
    int startIndex = -1;
    int endIndex = -1;
    startIndex = query.indexOf("COALESCE(", coalesceBegin);
    if (startIndex == -1)
      return query;
    else
      startIndex = startIndex + 9;
    endIndex = coalesceEndIndex(startIndex, query);
    assert endIndex > 0;
    String paramString = query.substring(startIndex, endIndex);
    String[] params = paramString.split(",");
    for(int i = 0; i < params.length; ++ i) {
      params[i] = params[i].replace(" ", "");
    }
    String agg = aggNullToZero(params);
    if(agg != null) {
      query = query.replace(query.substring(startIndex - 9, endIndex+1), agg);
      return coalesceHandler(query, endIndex);
    }

    String caseWhen = "CASE WHEN ";
    for(int i = 0; i < params.length; ++ i) {
      String param = params[i];
      if (i == params.length - 1) {
        caseWhen = caseWhen + "ELSE " + param + " ";
      } else {
        caseWhen = caseWhen + param + " IS NOT NULL ";
        caseWhen = caseWhen + "THEN " + param + " ";
      }
    }
    caseWhen += " END";
    query = query.replace(query.substring(startIndex - 9, endIndex+1), caseWhen);
    return coalesceHandler(query, endIndex);
  }

  private static String aggNatHandler(String str) {
    if(!str.contains("SUM(2)") && !str.contains("SUM(3)")) return str;
    String sum2SubQuery = "SELECT DEPTNO, JOB, SUM(2) AS EXPR$2 FROM EMP GROUP BY DEPTNO, JOB";
    String newSum2SubQuery = "SELECT DEPTNO, JOB, COUNT(*)+COUNT(*) AS e2 FROM EMP GROUP BY DEPTNO, JOB";

    return newSum2SubQuery;
    /*
    String sum3SubQuery = "SELECT DEPTNO, JOB, SUM(3) AS EXPR$2 FROM EMP GROUP BY DEPTNO, JOB";
    String newSum3SubQuery = "SELECT DEPTNO, JOB, COUNT(*) AS e2 FROM EMP GROUP BY DEPTNO, JOB";

    String result = str.replace("SUM(EXPR$2)", "SUM(e2)");
    result = result.replace(sum2SubQuery, newSum2SubQuery);
    result = result.replace(sum3SubQuery, newSum3SubQuery);
    return result;
     */
  }

  private static String replaceSumCastNull(String str, int start) {
    int end = str.indexOf("(", start) ;
    assert end > 0;
    int flag = 1;
    end++;
    for (; flag != 0; ++ end) {
      char curChar = str.charAt(end);
      if (curChar == '(')
        flag ++;
      else if (curChar == ')')
        flag --;
    }
    return str.replace(str.substring(start, end), "NULL");
  }

  private static String aggNullHandler(String str) {
    str = str.replace("SUM(NULL)", "NULL");
    int start = str.indexOf("SUM(CAST(NULL AS");
    while (start >= 0) {
      str = replaceSumCastNull(str, start);
      start = str.indexOf("SUM(CAST(NULL AS");
    }
    return str;
  }

  private static boolean isHaveAggregate(String str) {
    if(str.contains("HAVING"))
      return str.substring(str.indexOf("HAVING")).contains("COUNT") ||
             str.substring(str.indexOf("HAVING")).contains("AVG") ||
             str.substring(str.indexOf("HAVING")).contains("MIN") ||
             str.substring(str.indexOf("HAVING")).contains("MAX") ||
             str.substring(str.indexOf("HAVING")).contains("SUM");
    return false;
  }

  public static String havingHandler(String query) {
    if(!isHaveAggregate(query))
      return query;
    final Rewriter rewriter = new Rewriter();
    try{
      query = rewriter.transform(rewriter.getSqlNode(query), Rewriter.rewriteType.HAVING);
    } catch (Exception e) {
    }
    return query;
  }

  private static boolean isWithAs(String str) {
    String regex = ".*WITH\\s+\\w+(\\d*)\\s+AS.*";
    return str.matches(regex);
  }

  public static String withAsHandler(String query) {
    if(!isWithAs(query))
      return query;
    final Rewriter rewriter = new Rewriter();
    try{
      query = rewriter.transform(rewriter.getSqlNode(query), Rewriter.rewriteType.WITHAS);
    } catch (Exception e) {
    }
    return query;
  }

  private static String aggArithHandler(String query) {
    final String regex = ".*[SUM|MAX|MIN|COUNT|AVG]\\(.*\\)\s[\\+|\\-|\\*|\\/]\s\\d.*";
    if(!query.matches((regex)))
      return  query;
    final Rewriter rewriter = new Rewriter();
    try{
      query = rewriter.transform(rewriter.getSqlNode(query), Rewriter.rewriteType.AGGARITH);
    } catch (Exception e) {
      System.out.println(e);
    }
    return query;
  }

  private static String aggGroupByHandler(String query) {
    final Rewriter rewriter = new Rewriter(query);
    try{
      query = rewriter.transform(rewriter.getSqlNode(query), Rewriter.rewriteType.AGGGROUPBY);
    } catch (Exception e) {
      return query;
    }
    return query;
  }

  private static String dateFormatHandler(String query) {
    // calcite parser cannot parse; string processing
    // date('yyyy-MM-DD +xx') -> date 'yyyy-MM-DD'
    StringBuilder sb = new StringBuilder();
    Pattern pattern = Pattern.compile("date\\('[0-9]{4}-[0-9]{2}-[0-9]{2} +\\+[0-9]+'\\)", Pattern.CASE_INSENSITIVE);
    Matcher matcher = pattern.matcher(query);
    int lastEnd = 0;
    while (matcher.find()) {
      int start = matcher.start(), end = matcher.end();
      // unmatched part remains unchanged
      sb.append(query, lastEnd, start);
      // matched part is to be modified
      String sub = matcher.group()
              .replaceAll(" *\\+[0-9]+'", "'")
              .replace('(', ' ')
              .replace(')', ' ');
      sb.append(sub);
      // next loop
      lastEnd = end;
    }
    sb.append(query.substring(lastEnd));
    return sb.toString();
  }

  public static String test(String query) {
    final Rewriter rewriter = new Rewriter();
    try{
      rewriter.getSqlNode(query);
    } catch (Exception e) {
      System.out.println(e);
    }
    return query;
  }

  public static String parsePreprocess(String str) {
    // replace $
    // queries with VALUES skip the replacement of $
    if (!str.toUpperCase().contains("_DOLLAR_") && !str.toUpperCase().contains("VALUES"))
      str = str.replace("$", "_DOLLAR_");
    // handlers/rewriters
    str = SemiAntiJoinHandler.handle(str);
    str = CastHandler.handle(str);
    str = coalesceHandler(str, 0);
//    str = aggNatHandler(str);
    str = aggNullHandler(str);
    str = havingHandler(str);
    str = withAsHandler(str);
    //str = aggArithHandler(str);
    str = aggGroupByHandler(str);
    str = dateFormatHandler(str);
    str = SqlNodePreprocess.preprocessAll(str);
    return str;
  }

  public static String[] parseCoPreprocess(String str0, String str1) {
    return SqlNodeCoPreprocess.coPreprocessAll(str0, str1);
  }

  public static SqlNode parseSql(String dbType, String sql) {
    try {
      return AstParser.ofDb(dbType).parse(sql);
    } catch (ParseCancellationException ex) {
      if (!PARSING_ERROR_MUTED) System.err.println(ex.getMessage());
      return null;
    }
  }

  public static String quoted(String dbType, String name) {
    if (MySQL.equals(dbType)) return '`' + name + '`';
    else if (PostgreSQL.equals(dbType)) return '"' + name + '"';
    else if (SQLServer.equals(dbType)) return '[' + name + ']';
    else throw new IllegalArgumentException("unknown db type: " + dbType);
  }

  public static List<String> splitSql(String str) {
    final List<String> list = new ArrayList<>(str.length() / 100);

    boolean inSql = false;
    boolean inQuote = false;
    boolean inComment = false;
    boolean escape = false;
    boolean hyphen = false;
    int start = 0;

    for (int i = 0; i < str.length(); i++) {
      final char c = str.charAt(i);

      if (inComment) {
        assert !inSql;
        if (c == '\n' || c == '\r') inComment = false;
        continue;
      }

      if (!inSql) {
        if (Character.isSpaceChar(c) || c == '\n' || c == '\r') continue;
        else {
          inSql = true;
          start = i;
        }
      }

      if (c != '-') hyphen = false;

      switch (c) {
        case '\\':
          escape = true;
          continue;

        case '`':
        case '"':
        case '\'':
          if (!escape) inQuote = !inQuote;
          break;

        case '-':
          if (!inQuote) {
            if (!hyphen) hyphen = true;
            else {
              if (start < i - 1) list.add(str.substring(start, i - 1));
              inComment = true;
              inSql = false;
              hyphen = false;
            }
          }
          continue;

        case ';':
          if (!inQuote) list.add(str.substring(start, i));
          inSql = false;
          break;
      }
      escape = false;
    }

    if (inSql) list.add(str.substring(start));

    return list;
  }

  public static String simpleName(String name) {
    return name == null ? null : unquoted(unquoted(name, '"'), '`').toLowerCase();
  }

  public static int[] idsOf(List<SqlNode> nodes) {
    final int[] ids = new int[nodes.size()];
    for (int i = 0, bound = nodes.size(); i < bound; i++) {
      ids[i] = nodes.get(i).nodeId();
    }
    return ids;
  }

  public static SqlCopier copyAst(SqlNode node) {
    return new SqlCopier().root(node);
  }

  public static SqlNode copyAst(SqlNode node, SqlContext toCtx) {
    return new SqlCopier().root(node).to(toCtx).go();
  }

  public static String dumpAst(SqlNode root) {
    return dumpAst(root, new StringBuilder(), 0).toString();
  }

  public static StringBuilder dumpAst(SqlNode root, StringBuilder builder) {
    return dumpAst(root, builder, 0);
  }

  private static StringBuilder dumpAst(SqlNode root, StringBuilder builder, int level) {
    if (root == null) return builder;

    final SqlContext context = root.context();
    final LabeledTreeFields<SqlKind> fields = context.fieldsOf(root.nodeId());

    builder.append(" ".repeat(level)).append(root.nodeId()).append(' ').append(root.kind());
    builder.append('\n');

    if (fields == null) return builder;

    for (Map.Entry<FieldKey<?>, Object> pair : fields.entrySet()) {
      final FieldKey<?> key = pair.getKey();
      final Object value = pair.getValue();
      if (value instanceof SqlNode || value instanceof SqlNodes) continue;
      builder.append(" ".repeat(level + 1)).append(key).append('=').append(value).append('\n');
    }

    for (Map.Entry<FieldKey<?>, Object> pair : fields.entrySet()) {
      final FieldKey<?> key = pair.getKey();
      final Object value = pair.getValue();
      if (value instanceof SqlNode) {
        builder.append(" ".repeat(level + 1)).append(key).append('=').append('\n');
        dumpAst((SqlNode) value, builder, level + 1);
      }
    }

    for (Map.Entry<FieldKey<?>, Object> pair : fields.entrySet()) {
      final FieldKey<?> key = pair.getKey();
      final Object value = pair.getValue();
      if (value instanceof SqlNodes) {
        builder.append(" ".repeat(level + 1)).append(key).append('=').append('\n');
        for (SqlNode child : ((SqlNodes) value)) {
          dumpAst(child, builder, level + 1);
        }
      }
    }

    return builder;
  }

  public static SqlNode mkName2(SqlContext ctx, String piece0, String piece1) {
    final SqlNode node = SqlNode.mk(ctx, SqlKind.Name2);
    if (piece0 != null) node.$(SqlNodeFields.Name2_0, piece0);
    node.$(SqlNodeFields.Name2_1, piece1);
    return node;
  }

  public static SqlNode mkTableName(SqlContext ctx, String tableName) {
    final SqlNode nameNode = SqlNode.mk(ctx, SqlKind.TableName);
    nameNode.$(SqlNodeFields.TableName_Table, tableName);
    return nameNode;
  }

  public static SqlNode mkColName(SqlContext ctx, String qualification, String name) {
    final SqlNode colName = SqlNode.mk(ctx, SqlKind.ColName);
    colName.$(SqlNodeFields.ColName_Table, qualification);
    colName.$(SqlNodeFields.ColName_Col, name);
    return colName;
  }

  public static SqlNode mkColRef(SqlContext ctx, String qualification, String name) {
    final SqlNode colName = mkColName(ctx, qualification, name);
    final SqlNode colRef = SqlNode.mk(ctx, ExprKind.ColRef);
    colRef.$(ExprFields.ColRef_ColName, colName);
    return colRef;
  }

  public static SqlNode mkWildcard(SqlContext ctx, String tableName) {
    final SqlNode wildcard = SqlNode.mk(ctx, ExprKind.Wildcard);
    if (tableName != null) wildcard.$(ExprFields.Wildcard_Table, mkTableName(ctx, tableName));
    return wildcard;
  }

  public static SqlNode mkUnary(SqlContext ctx, UnaryOpKind op, SqlNode operand) {
    expect(operand, SqlKind.Expr);
    final SqlNode unary = SqlNode.mk(ctx, ExprKind.Unary);
    unary.$(ExprFields.Unary_Op, op);
    unary.$(ExprFields.Unary_Expr, operand);
    return unary;
  }

  public static SqlNode mkBinary(SqlContext ctx, BinaryOpKind op, SqlNode lhs, SqlNode rhs) {
    expect(lhs, SqlKind.Expr);
    expect(rhs, SqlKind.Expr);

    final SqlNode binary = SqlNode.mk(ctx, ExprKind.Binary);
    binary.$(ExprFields.Binary_Op, op);
    binary.$(ExprFields.Binary_Left, lhs);
    binary.$(ExprFields.Binary_Right, rhs);
    return binary;
  }

  public static SqlNode mkFuncCall(SqlContext ctx, String funcName, List<SqlNode> args) {
    final SqlNode funcCall = SqlNode.mk(ctx, ExprKind.FuncCall);
    final SqlNodes argPack = SqlNodes.mk(ctx, args);
    funcCall.$(ExprFields.FuncCall_Name, mkName2(ctx, null, funcName));
    funcCall.$(ExprFields.FuncCall_Args, argPack);
    return funcCall;
  }

  public static SqlNode mkSelectItem(SqlContext ctx, SqlNode expr, String alias) {
    expect(expr, SqlKind.Expr);

    final SqlNode selectItem = SqlNode.mk(ctx, SqlKind.SelectItem);
    selectItem.$(SqlNodeFields.SelectItem_Expr, expr);
    if (alias != null) selectItem.$(SqlNodeFields.SelectItem_Alias, alias);
    return selectItem;
  }

  public static SqlNode mkLiteral(SqlContext ctx, LiteralKind kind, Object value) {
    final SqlNode literal = SqlNode.mk(ctx, ExprKind.Literal);
    literal.$(ExprFields.Literal_Kind, kind);
    literal.$(ExprFields.Literal_Value, value);
    return literal;
  }

  public static SqlNode mkQueryExpr(SqlContext ctx, SqlNode query) {
    expect(query, SqlKind.Query);
    final SqlNode expr = SqlNode.mk(ctx, ExprKind.QueryExpr);
    expr.$(ExprFields.QueryExpr_Query, query);
    return expr;
  }

  public static SqlNode mkConjunction(SqlContext ctx, Iterable<SqlNode> filters) {
    SqlNode expr = null;
    for (SqlNode filter : filters) {
      expect(filter, SqlKind.Expr);
      if (expr == null) expr = filter;
      else expr = mkBinary(ctx, AND, expr, filter);
    }
    return expr;
  }

  public static SqlNode mkSimpleSource(SqlContext ctx, String tableName, String alias) {
    final SqlNode nameNode = mkTableName(ctx, tableName);
    final SqlNode tableSourceNode = SqlNode.mk(ctx, TableSourceKind.SimpleSource);
    tableSourceNode.$(TableSourceFields.Simple_Table, nameNode);
    tableSourceNode.$(TableSourceFields.Simple_Alias, alias);
    return tableSourceNode;
  }

  public static SqlNode mkJoinSource(
      SqlContext ctx, SqlNode lhs, SqlNode rhs, SqlNode cond, JoinKind kind) {
    expect(lhs, SqlKind.TableSource);
    expect(rhs, SqlKind.TableSource);

    final SqlNode joinNode = SqlNode.mk(ctx, TableSourceKind.JoinedSource);
    joinNode.$(TableSourceFields.Joined_Left, lhs);
    joinNode.$(TableSourceFields.Joined_Right, rhs);
    joinNode.$(TableSourceFields.Joined_On, cond);
    joinNode.$(TableSourceFields.Joined_Kind, kind);
    return joinNode;
  }

  public static SqlNode mkDerivedSource(SqlContext ctx, SqlNode query, String alias) {
    expect(query, SqlKind.Query);
    final SqlNode sourceNode = SqlNode.mk(ctx, TableSourceKind.DerivedSource);
    sourceNode.$(TableSourceFields.Derived_Subquery, query);
    sourceNode.$(TableSourceFields.Derived_Alias, alias);
    return sourceNode;
  }

  public static SqlNode mkSetOp(SqlContext ctx, SqlNode lhs, SqlNode rhs, SetOpKind kind) {
    expect(lhs, SqlKind.Query);
    expect(rhs, SqlKind.Query);

    final SqlNode setOpNode = SqlNode.mk(ctx, SqlKind.SetOp);
    setOpNode.$(SqlNodeFields.SetOp_Left, lhs);
    setOpNode.$(SqlNodeFields.SetOp_Right, rhs);
    setOpNode.$(SqlNodeFields.SetOp_Kind, kind);
    return setOpNode;
  }

  public static SqlNode mkQuery(SqlContext ctx, SqlNode body) {
    if (!SqlKind.QuerySpec.isInstance(body) && !SqlKind.SetOp.isInstance(body))
      throw new IllegalArgumentException("invalid query body: " + body.kind());

    final SqlNode q = SqlNode.mk(ctx, SqlKind.Query);
    q.$(SqlNodeFields.Query_Body, body);
    return q;
  }

  public static SqlNode mkAggregate(SqlContext ctx, List<SqlNode> args, String aggFuncName) {
    final SqlNodes argPack = SqlNodes.mk(ctx, args);
    final SqlNode aggregate = SqlNode.mk(ctx, ExprKind.Aggregate);
    aggregate.$(ExprFields.Aggregate_Name, aggFuncName);
    aggregate.$(ExprFields.Aggregate_Args, argPack);
    return aggregate;
  }

  public static boolean isAggregate(SqlNode expr) {
    return expr.$(ExprFields.Aggregate_Name) != null;
  }

  public static boolean isColRefEq(SqlNode ast) {
    return ExprKind.Binary.isInstance(ast)
        && EQUAL == ast.$(ExprFields.Binary_Op)
        && ExprKind.ColRef.isInstance(ast.$(ExprFields.Binary_Left))
        && ExprKind.ColRef.isInstance(ast.$(ExprFields.Binary_Right));
  }

  /** Check if the ast is of the form "col0 = const_value", where const_value is not "NULL" */
  public static boolean isEquiConstPredicate(SqlNode ast) {
    final SqlNode lhs = ast.$(ExprFields.Binary_Left);
    final SqlNode rhs = ast.$(ExprFields.Binary_Right);
    final BinaryOpKind op = ast.$(ExprFields.Binary_Op);

    final SqlNode literal;
    if (ExprKind.ColRef.isInstance(lhs) && ExprKind.Literal.isInstance(rhs)) literal = rhs;
    else if (ExprKind.ColRef.isInstance(rhs) && ExprKind.Literal.isInstance(lhs)) literal = lhs;
    else return false;

    return (op == IS || op == EQUAL || op == NULL_SAFE_EQUAL)
        && literal.$(ExprFields.Literal_Kind) != LiteralKind.NULL;
  }

  /** Check if the ast is of the form "col0 = col1 [AND col2 = col3 [AND ...]]" */
  public static boolean isEquiJoinPredicate(SqlNode ast) {
    if (!ExprKind.Binary.isInstance(ast)) return false;
    final BinaryOpKind op = ast.$(ExprFields.Binary_Op);
    if (op == BinaryOpKind.AND) {
      return isEquiJoinPredicate(ast.$(ExprFields.Binary_Left))
          && isEquiJoinPredicate(ast.$(ExprFields.Binary_Right));
    } else {
      return isColRefEq(ast);
    }
  }

  public static boolean isPrimitivePredicate(SqlNode ast) {
    return SqlKind.Expr.isInstance(ast)
        && (!ExprKind.Binary.isInstance(ast) || !ast.$(ExprFields.Binary_Op).isLogic())
        && (!ExprKind.Unary.isInstance(ast) || !ast.$(ExprFields.Unary_Op).isLogic());
  }

  public static SqlNode getAnotherSide(SqlNode binaryExpr, SqlNode thisSide) {
    if (!ExprKind.Binary.isInstance(binaryExpr)) return null;
    final SqlNode lhs = binaryExpr.$(ExprFields.Binary_Left);
    final SqlNode rhs = binaryExpr.$(ExprFields.Binary_Right);
    if (nodeEquals(lhs, thisSide)) return rhs;
    if (nodeEquals(rhs, thisSide)) return lhs;
    return null;
  }

  public static String selectItemNameOf(SqlNode selectItem) {
    expect(selectItem, SqlKind.SelectItem);
    final String alias = selectItem.$(SqlNodeFields.SelectItem_Alias);
    if (alias != null) return alias;

    final SqlNode exprAst = selectItem.$(SqlNodeFields.SelectItem_Expr);
    if (ExprKind.ColRef.isInstance(exprAst))
      return exprAst.$(ExprFields.ColRef_ColName).$(SqlNodeFields.ColName_Col);
    return null;
  }

  public static List<SqlNode> linearizeConjunction(SqlNode expr) {
    expect(expr, SqlKind.Expr);
    return linearizeConjunction(expr, new ArrayList<>(5));
  }

  public static List<SqlNode> linearizeConjunction(SqlNode expr, List<SqlNode> terms) {
    final BinaryOpKind op = expr.$(ExprFields.Binary_Op);
    if (op != AND) terms.add(expr);
    else {
      linearizeConjunction(expr.$(ExprFields.Binary_Left), terms);
      linearizeConjunction(expr.$(ExprFields.Binary_Right), terms);
    }
    return terms;
  }

  private static void expect(SqlNode node, TableSourceKind expected) {
    if (!expected.isInstance(node))
      throw new IllegalArgumentException(
          "expect " + expected + ", but get " + node.$(SqlNodeFields.TableSource_Kind));
  }

  private static void expect(SqlNode node, ExprKind expected) {
    if (!expected.isInstance(node))
      throw new IllegalArgumentException(
          "expect " + expected + ", but get " + node.$(SqlNodeFields.Expr_Kind));
  }

  private static void expect(SqlNode node, SqlKind expected) {
    if (!expected.isInstance(node))
      throw new IllegalArgumentException("expect " + expected + ", but get " + node.kind());
  }
}

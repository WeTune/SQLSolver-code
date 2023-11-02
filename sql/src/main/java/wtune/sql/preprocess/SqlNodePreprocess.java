package wtune.sql.preprocess;

import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.sql.parser.SqlParser;
import org.apache.calcite.sql.validate.SqlConformanceEnum;
import org.apache.calcite.tools.FrameworkConfig;
import org.apache.calcite.tools.Frameworks;
import org.apache.calcite.tools.Planner;
import wtune.sql.schema.Schema;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Entry of preprocessing SqlNodes (Calcite),
 * and the parent class of all rewriters that
 * rewrite SqlNodes.
 */
public abstract class SqlNodePreprocess {

  private static FrameworkConfig config;

  private static List<SqlNodePreprocess> rewriters = null;
  private static Schema schema;

  // parser config
  static {
    Frameworks.ConfigBuilder builder = Frameworks.newConfigBuilder();
    SqlParser.ConfigBuilder parserConfigBuilder =
      SqlParser.configBuilder().setConformance(SqlConformanceEnum.BABEL);
    builder.parserConfig(parserConfigBuilder.build());
    config = builder.build();
  }

  /** HINT: Add new SqlNode preprocessors HERE. */
  private static void registerPreprocessors() {
    rewriters.add(new NEQRewriter());
    rewriters.add(new OrEquationsRewriter());
    rewriters.add(new NotNullInferer());
    rewriters.add(new DateOpRewriter());
    rewriters.add(new ExtractYearRewriter());
    rewriters.add(new DateConstantRewriter());
    rewriters.add(new BetweenAndRewriter());
    rewriters.add(new NumericConstantRewriter());
    rewriters.add(new NumericComparisonRewriter());
    rewriters.add(new SemiAntiJoinRewriter());
    rewriters.add(new ScalarQueryRewriter());
    rewriters.add(new HavingAggRewriter());
    rewriters.add(new PredExprRewriter());
    rewriters.add(new CountArgsRewriter());
    rewriters.add(new AggFilterRewriter());
    rewriters.add(new AggSelectGroupRewriter());
    rewriters.add(new RollupRewriter());
    rewriters.add(new GroupingSetsRewriter());
    rewriters.add(new CastRewriter());
    rewriters.add(new AggGroupRewriter());
    rewriters.add(new CompoundAggRewriter());
    rewriters.add(new AggExprRewriter());
    rewriters.add(new ConstantRowRewriter());
  }

  public static void setSchema(Schema s) {
    schema = s;
  }

  public static Schema getSchema() {
    return schema;
  }

  /**
   * Apply all the registered preprocessors one by one
   * to preprocess the given query.
   * @param sql the SQL query to be preprocessed
   * @return the query after preprocessed by all registered preprocessors
   */
  public static String preprocessAll(String sql) {
    Planner planner = Frameworks.getPlanner(config);
    try {
      // string -> sqlnode
      sql = sql.replace('\"', '\'').replace(';', ' ');
      SqlNode node = planner.parse(sql);
      String strOld = node.toString();
      // preprocess sqlnode
      node = preprocessAll(node); // noexcept
      // sqlnode -> string
      String strNew = node.toString();
//      System.out.println( "\n" +sql);
//      System.out.println(strOld + "\n" + strNew);
//      if (strNew.equals(strOld)) {
//        // unchanged
//        return postProcess(sql);
//      }
      strNew = postProcess(strNew);
      return strNew;
    } catch (Exception e) {
      // stay unchanged upon exception
      return sql;
    }
  }

  // process SQL text after preprocessing
  private static String postProcess(String sql) {
    sql = sql.replace("\n", " ").replace("\r", " ").replace("`", "");
    sql = removeRow(sql);
    sql = turnFetchNextToLimit(sql);
    sql = removeROWSInOffset(sql);
    return sql;
  }

  // "ROW(a, b) IN ..." (invalid) -> "(a, b) IN ..." (valid)
  // remove ROW directly
  private static String removeRow(String str) {
    Pattern pattern = Pattern.compile("ROW\\([A-Z0-9]+\\.[A-Z0-9]+(, [A-Z0-9]+\\.[A-Z0-9]+)*\\)");
    Matcher matcher = pattern.matcher(str);
    while (matcher.find()) {
      int pos = matcher.start();
      str = str.substring(0, pos) + str.substring(pos + 3);
      pattern = Pattern.compile("ROW\\([A-Z0-9]+\\.[A-Z0-9]+(, [A-Z0-9]+\\.[A-Z0-9]+)*\\)");
      matcher = pattern.matcher(str);
    }
    return str;
  }

  // "FETCH NEXT n ROWS ONLY" -> "LIMIT n"
  private static String turnFetchNextToLimit(String str) {
    Pattern pattern = Pattern.compile("FETCH NEXT [0-9]+ ROWS ONLY");
    Matcher matcher = pattern.matcher(str);
    while (matcher.find()) {
      int start = matcher.start(), end = matcher.end();
      String num = str.substring(start + 11, end - 10);
      String limit = "LIMIT " + num;
      str = str.substring(0, start) + limit + str.substring(end);
      pattern = Pattern.compile("FETCH NEXT [0-9]+ ROWS ONLY");
      matcher = pattern.matcher(str);
    }
    return str;
  }

  private static String removeROWSInOffset(String str) {
    Pattern pattern = Pattern.compile("OFFSET [0-9]+ ROWS");
    Matcher matcher = pattern.matcher(str);
    while (matcher.find()) {
      int start = matcher.start(), end = matcher.end();
      String num = str.substring(start + 11, end - 10);
      String limit = "OFFSET " + num;
      str = str.substring(0, start) + limit + str.substring(end);
      pattern = Pattern.compile("OFFSET [0-9]+ ROWS");
      matcher = pattern.matcher(str);
    }
    return str;
  }

  private static synchronized void init() {
    if (rewriters == null) {
      rewriters = new ArrayList<>();
      registerPreprocessors();
    }
  }

  /**
   * Call all the registered preprocessors one by one
   * to preprocess the given SqlNode.
   * @param node the SqlNode to be preprocessed
   * @return the SqlNode after preprocessed by all registered preprocessors
   */
  public static SqlNode preprocessAll(SqlNode node) {
    init();
    for (SqlNodePreprocess rewriter : rewriters) {
      try {
        node = rewriter.preprocess(node);
      } catch (Exception e) {
        // keep the last result upon exception
        e.printStackTrace();
      }
    }
    return node;
  }

  /**
   * A template method which should preprocess a given SqlNode.
   * @param node the SqlNode to be preprocessed
   * @return the SqlNode after preprocessing
   */
  public abstract SqlNode preprocess(SqlNode node);
}

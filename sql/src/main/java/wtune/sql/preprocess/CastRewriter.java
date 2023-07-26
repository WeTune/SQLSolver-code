package wtune.sql.preprocess;

import org.apache.calcite.sql.SqlNode;
import org.apache.calcite.tools.FrameworkConfig;
import org.apache.calcite.tools.Frameworks;
import org.apache.calcite.tools.Planner;

public class CastRewriter extends SqlNodePreprocess {

  @Override
  public SqlNode preprocess(SqlNode node) {
    // SqlNode -> SQL
    String sql = node.toString().replace("\n", " ").replace("`", ""), newSql;
    if (!sql.contains("CAST")) return node;
    // handle
    try {
      newSql = CastHandler.handle(sql);
    } catch (Exception e) {
      return node;
    }
    if (sql.equals(newSql)) return node;
    // SQL -> SqlNode
    FrameworkConfig config = Frameworks.newConfigBuilder().build();
    Planner planner = Frameworks.getPlanner(config);
    try {
      return planner.parse(newSql);
    } catch (Exception e) {
      // stay unchanged upon exception
      return node;
    }
  }

}

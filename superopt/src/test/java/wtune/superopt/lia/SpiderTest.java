package wtune.superopt.lia;

import org.junit.jupiter.api.Test;
import wtune.sql.SqlSupport;
import wtune.sql.ast.SqlNode;
import wtune.sql.plan.*;
import wtune.sql.preprocess.SqlNodePreprocess;
import wtune.sql.schema.Schema;
import wtune.sql.support.action.NormalizationSupport;
import wtune.stmt.App;
import wtune.superopt.logic.CASTSupport;
import wtune.superopt.logic.LogicSupport;
import wtune.superopt.logic.SqlSolver;
import wtune.superopt.uexpr.UExprConcreteTranslationResult;
import wtune.superopt.uexpr.UExprSupport;
import wtune.superopt.uexpr.normalizer.QueryUExprICRewriter;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static wtune.common.datasource.DbSupport.MySQL;
import static wtune.sql.SqlSupport.*;
import static wtune.sql.plan.PlanSupport.*;
import static wtune.superopt.logic.LogicSupport.*;
public class SpiderTest {

    @Test
    void testLiaOnExampleSql() throws IOException {
        LogicSupport.setDumpLiaFormulas(true);
    QueryPair pair =
        readPair(
            "SELECT Name FROM country WHERE Continent  =  \"Asia\"  AND population  >  (SELECT min(population) FROM country WHERE Continent  =  \"Africa\")",
            "SELECT Name FROM country WHERE Continent = 'Asia' AND Population > (SELECT max(Population) FROM country WHERE Continent = 'Africa')",
            "spider_world_1");
        SqlSolver.initialize();
        QueryUExprICRewriter.selectIC(-1);

        System.out.println(pair.sql0 + "\n" + pair.sql1);
        System.out.println(pair.p0 + "\n" + pair.p1);
        if (pair.p0 == null || pair.p1 == null) {
            System.out.println("Rule is: UNKNOWN");
        }else if (isLiteralEq(pair.p0, pair.p1)){
            System.out.println("Rule is: EQ");
        }else {
            final String res1 = getCalciteVerifyResultConcrete(pair, true);
            // final String res0 = getCalciteVerifyResultSymbolic(pair, false);
            System.out.println("[Concrete] Rule is: " + res1);
            // System.out.println("[Symbolic] Rule id " + pair.pairId() + " is: EQ");
        }
    }

    private String getCalciteVerifyResultConcrete(QueryPair pair, boolean verbose) {
        try {
            if (pair.sql0.contains("VALUES") || pair.sql1.contains("VALUES")) {
                final UExprConcreteTranslationResult uExprs
                        = UExprSupport.translateQueryWithVALUESToUExpr(pair.sql0, pair.sql1, pair.schema, 0);
                if (uExprs == null) {
                    return LogicSupport.stringifyResult(NEQ);
                }
                final int result = LogicSupport.proveEqByLIAStar(uExprs);
                return LogicSupport.stringifyResult(result);
            }
            final int result = LogicSupport.proveEqByLIAStarConcrete(pair.p0, pair.p1);
            return LogicSupport.stringifyResult(result);
        } catch (Exception exception) {
            if (verbose) exception.printStackTrace();
            return "exception";
        } catch (Error error) {
            if (verbose) error.printStackTrace();
            return "error";
        }
    }

    private QueryPair readPair(String sql0, String sql1, String appName) {
        final App app = App.of(appName);
        final Schema schema = app.schema("base");
        SqlNodePreprocess.setSchema(schema);
        CASTSupport.setSchema(schema);
        SqlSupport.muteParsingError();

        sql0 = parsePreprocess(sql0);
        sql1 = parsePreprocess(sql1);
        String[] pair = parseCoPreprocess(sql0, sql1);
        sql0 = pair[0];
        sql1 = pair[1];
        final SqlNode q0 = parseSql(MySQL, sql0);
        final SqlNode q1 = parseSql(MySQL, sql1);
        if (q0 == null) {
//        System.err.printf("Rule id: %d has unsupported query at line %d \n", ruleId, i + 1);
            return new QueryPair(schema, sql0, sql1);
        }
        if (q1 == null) {
//        System.err.printf("Rule id: %d has unsupported query at line %d \n", ruleId, i + 2);
            return new QueryPair(schema, sql0, sql1);
        }
        q0.context().setSchema(schema);
        q1.context().setSchema(schema);
        NormalizationSupport.normalizeAst(q0);
        NormalizationSupport.normalizeAst(q1);

        final PlanContext p0 = assemblePlan(q0, schema);
        if (p0 == null) {
//        System.err.printf("Rule id: %d has wrong query at line %d \n", ruleId, i + 1);
//        System.err.println(getLastError());
            return new QueryPair(schema, sql0, sql1, q0, q1);
        }


        final PlanContext p1 = assemblePlan(q1, schema);
        if (p1 == null) {
//        System.err.printf("Rule id: %d has wrong query at line %d \n", ruleId, i + 2);
//        System.err.println(getLastError());
            return new QueryPair(schema, sql0, sql1, q0, q1);
        }

        return new QueryPair(schema, sql0, sql1, q0, q1, p0, p1);
    }

    private static class QueryPair {
        private final Schema schema;
        private final String sql0, sql1;
        private final SqlNode q0, q1;
        private final PlanContext p0, p1;

        private QueryPair(Schema schema, String sql0, String sql1) {
            this(schema, sql0, sql1, null, null, null, null);
        }

        private QueryPair(Schema schema, String sql0, String sql1, SqlNode q0, SqlNode q1) {
            this(schema, sql0, sql1, q0, q1, null, null);
        }

        private QueryPair(
                Schema schema,
                String sql0, String sql1,
                SqlNode q0, SqlNode q1,
                PlanContext p0, PlanContext p1) {
            this.schema = schema;
            this.sql0 = sql0;
            this.sql1 = sql1;
            this.q0 = q0;
            this.q1 = q1;
            this.p0 = p0;
            this.p1 = p1;
        }
    }
}

package wtune.superopt.logic;

import wtune.sql.plan.*;
import wtune.sql.schema.Schema;
import wtune.sql.util.CastRemover;


public class CASTSupport {

  private final PlanContext plan0, plan1;

  public static Schema schema;

  CASTSupport(PlanContext p0, PlanContext p1) {
    plan0 = p0;
    plan1 = p1;
  }

  public static void setSchema(Schema s) {
    schema = s;
  }

  public static boolean castHandler(PlanContext p0, PlanContext p1) {
    CASTSupport castSupprt = new CASTSupport(p0, p1);
    return castSupprt.handler();
  }

  private boolean handler() {
    CastRemover.removeUselessCast(plan0);
    CastRemover.removeUselessCast(plan1);
    // TODO: add check
    return true;
  }

}

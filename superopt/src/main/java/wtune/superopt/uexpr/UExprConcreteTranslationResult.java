package wtune.superopt.uexpr;

import wtune.sql.plan.PlanContext;
import wtune.sql.plan.Value;
import wtune.sql.schema.Column;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static wtune.common.utils.IterableSupport.zip;
import static wtune.sql.plan.PlanSupport.tryResolveColumn;
import static wtune.superopt.uexpr.UExprConcreteTranslator.getFullName;

public class UExprConcreteTranslationResult {
  final PlanContext p0, p1;
  UTerm srcExpr, tgtExpr;
  UVar srcOutVar, tgtOutVar;
  final Map<UVar, List<Value>> srcTupleVarSchemas;
  final Map<UVar, List<Value>> tgtTupleVarSchemas;

  public UExprConcreteTranslationResult(PlanContext p0, PlanContext p1) {
    this.p0 = p0;
    this.p1 = p1;
    this.srcTupleVarSchemas = new HashMap<>();
    this.tgtTupleVarSchemas = new HashMap<>();
  }

  public UTerm sourceExpr() {
    return srcExpr;
  }

  public UTerm targetExpr() {
    return tgtExpr;
  }

  public UVar sourceOutVar() {
    return srcOutVar;
  }

  public UVar targetOutVar() {
    return tgtOutVar;
  }

  public void setSrcTupleVarSchema(UVar var, List<Value> schema) {
    srcTupleVarSchemas.put(var, schema);
  }

  public List<Value> srcTupleVarSchemaOf(UVar var) {
    return srcTupleVarSchemas.get(var);
  }

  public void setTgtTupleVarSchema(UVar var, List<Value> schema) {
    tgtTupleVarSchemas.put(var, schema);
  }

  public List<Value> tgtTupleVarSchemaOf(UVar var) {
    return tgtTupleVarSchemas.get(var);
  }

  public void alignOutVar(UVar freshOutVar) {
    // Invariant: out var is BASE type
    assert srcOutVar.is(UVar.VarKind.BASE) && tgtOutVar.is(UVar.VarKind.BASE);

    tgtExpr.replaceVarInplace(tgtOutVar, freshOutVar, false);
    tgtTupleVarSchemas.put(freshOutVar, tgtTupleVarSchemas.get(tgtOutVar));
    tgtTupleVarSchemas.remove(tgtOutVar);
    tgtOutVar = freshOutVar.copy();

    srcExpr.replaceVarInplace(srcOutVar, freshOutVar, false);
    srcTupleVarSchemas.put(freshOutVar, srcTupleVarSchemas.get(srcOutVar));
    srcTupleVarSchemas.remove(srcOutVar);
    srcOutVar = freshOutVar.copy();
  }

  public void alignOutSchema() {
    // srcOutVar and tgtOutVar should be aligned
    assert srcOutVar.is(UVar.VarKind.BASE) && srcOutVar.equals(tgtOutVar);
    final List<Value> srcOutVarSchema = srcTupleVarSchemas.get(srcOutVar);
    final List<Value> tgtOutVarSchema = tgtTupleVarSchemas.get(tgtOutVar);
    if (srcOutVarSchema.size() != tgtOutVarSchema.size())
      return; // Hack for some cases with VALUES, which has different length of schemas

    for (var schemaPair : zip(srcOutVarSchema, tgtOutVarSchema)) {
      final UVar srcOutProjVar = mkProjVarForOutVar(schemaPair.getLeft(), false);
      final UVar tgtOutProjVar = mkProjVarForOutVar(schemaPair.getRight(), true);
      if (!srcOutProjVar.equals(tgtOutProjVar)) {
        tgtExpr.replaceVarInplace(tgtOutProjVar, srcOutProjVar, false);
      }
    }
  }

  private UVar mkProjVarForOutVar(Value value, boolean isTarget) {
    final Column column = tryResolveColumn(isTarget ? p1 : p0, value);
    final UName projFullName = UName.mk(getFullName((column != null) ? column : value));
    return UVar.mkProj(projFullName, isTarget ? tgtOutVar : srcOutVar);
  }
}

package wtune.superopt.uexpr;

import wtune.sql.ast.constants.ConstraintKind;
import wtune.sql.schema.Column;
import wtune.sql.schema.Constraint;
import wtune.sql.schema.Table;
import wtune.superopt.logic.CASTSupport;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static wtune.common.utils.IterableSupport.any;
import static wtune.superopt.uexpr.UExprSupport.getSchemaEqVarCongruence;
import static wtune.superopt.uexpr.UExprSupport.transformTerms;
import static wtune.superopt.logic.CASTSupport.schema;

final class UPredImpl implements UPred {
  private PredKind predKind;
  private UName predName;
  private final List<UTerm> arguments;

  public UPredImpl(PredKind predKind, UName predName, List<UTerm> arguments) {
    if (predKind == PredKind.FUNC) assert arguments.size() == 1;
    else assert arguments.size() == 2;

    this.predKind = predKind;
    this.predName = predName;
    this.arguments = arguments;
  }

  @Override
  public List<UTerm> subTerms() {
    return arguments;
  }

  @Override
  public PredKind predKind() {
    return predKind;
  }

  @Override
  public UName predName() {
    return predName;
  }

  @Override
  public List<UTerm> args() {
    return arguments;
  }

  @Override
  public boolean isUsing(UVar var) {
    return any(arguments, arg -> arg.isUsing(var));
  }

  @Override
  public boolean isUsingProjVar(UVar var) {
    return any(arguments, arg -> arg.isUsingProjVar(var));
  }

  @Override
  public UTerm replaceVar(UVar baseVar, UVar repVar, boolean freshVar) {
    final List<UTerm> replaced = transformTerms(arguments, t -> t.replaceVar(baseVar, repVar, freshVar));
    return UPred.mk(predKind, predName, replaced);
  }

  @Override
  public boolean replaceVarInplace(UVar baseVar, UVar repVar, boolean freshVar) {
    boolean modified = false;
    for (UTerm arg : arguments) {
      if (arg.replaceVarInplace(baseVar, repVar, freshVar)) modified = true;
    }
    return modified;
  }

  @Override
  public boolean replaceVarInplaceWOPredicate(UVar baseVar, UVar repVar) {
    boolean modified = false;
    if(predKind == PredKind.EQ) {
      return false;
    }
    for (UTerm arg : arguments) {
      if (arg.replaceVarInplaceWOPredicate(baseVar, repVar)) modified = true;
    }
    return modified;
  }

  @Override
  public UTerm replaceAtomicTerm(UTerm baseTerm, UTerm repTerm) {
    assert baseTerm.kind().isTermAtomic();
    if (this.equals(baseTerm)) return repTerm.copy();
    final List<UTerm> replaced = transformTerms(arguments, t -> t.replaceAtomicTerm(baseTerm, repTerm));
    return UPred.mk(predKind, predName, replaced);
  }

  @Override
  public UTerm copy() {
    List<UTerm> copies = new ArrayList<>(arguments);
    for (int i = 0, bound = arguments.size(); i < bound; i++) {
      final UTerm copiedFactor = arguments.get(i).copy();
      copies.set(i, copiedFactor);
    }
    return UPred.mk(predKind, predName.copy(), copies);
  }

  @Override
  public String toString() {
    final StringBuilder builder = new StringBuilder(arguments.size() * 4);
    builder.append("[");
    if (isUnaryPred()) {
      // only one single arg
      assert arguments.size() == 1;
      builder.append(predName).append("(").append(arguments.get(0)).append(")");
    } else {
      assert arguments.size() == 2;
      builder.append(arguments.get(0));
      builder.append(" ").append(predName).append(" ");
      builder.append(arguments.get(1));
    }
    builder.append("]");
    return builder.toString();
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (!(obj instanceof UPred)) return false;

    UPred that = (UPred) obj;
    if (that.predKind() == PredKind.EQ) {
      UTerm lhs = that.args().get(0);
      UTerm rhs = that.args().get(1);
      if(lhs instanceof UPred && rhs instanceof UConst && ((UConst) rhs).value() == 1)
        that = (UPred) lhs;
    }

    if(predKind == PredKind.EQ) {
      UTerm lhs = args().get(0);
      UTerm rhs = args().get(1);
      if(lhs instanceof UPred && rhs instanceof UConst && ((UConst) rhs).value() == 1)
        return lhs.equals(that);
    }

    if (predKind != that.predKind() || !predName.equals(that.predName())) return false;

    if (isPredKind(PredKind.FUNC)) {
      assert arguments.size() == 1 && that.args().size() == 1;
      return arguments.get(0).equals(that.args().get(0));
    } else {
      assert arguments.size() == 2 && that.args().size() == 2;
      if (isPredKind(PredKind.EQ) || isPredKind(PredKind.NEQ)) // [t1 = t2] equals to [t2 = t1]
        return new HashSet<>(arguments).equals(new HashSet<>(that.args()));
      else return arguments.equals(that.args());
    }
  }

  @Override
  public int hashCode() {
    return predKind.hashCode() * 31 * 31 + predName.hashCode() * 31 + new HashSet<>(arguments).hashCode();
  }

  // 1 true 0 false -1 unknown
  public int isTruePred(UTerm expr) {
    switch (predKind) {
      case EQ : {
        UTerm v1 = arguments.get(0);
        UTerm v2 = arguments.get(1);
        if (v1.toString().equals(v2.toString()))
          return 1;
        if (v1 instanceof UConst && v2 instanceof UConst) {
          if(((UConst) v1).value() != ((UConst) v2).value()) {
            return 0;
          }
        }
        return -1; // unknown
      }
      case FUNC: {
        if (predName.equals(UName.NAME_IS_NULL)) {
          UTerm v1 = arguments.get(0);
          if(v1.kind() != UKind.VAR)
            return -1;
          final List<Constraint> notNulls = new ArrayList<>();
          for (Table table : schema.tables()) {
            table.constraints(ConstraintKind.NOT_NULL).forEach(notNulls::add);
          }
          UVar arg = ((UVarTerm) v1).var();

          if(expr == null) return -1;
//          System.out.println("constraint: " + notNulls);
          for(final Constraint notNull : notNulls) {
            for(final Column column : notNull.columns()) {
              if(arg.name().toString().equals(column.tableName()+"."+column.name())) {
                if (arg.args().length == 1) {
                  if(expr.toString().contains(column.tableName()+"("+arg.args()[0]+")"))
                    return 0;
                  else {
                    //natural congruence
                    String columnStr = column.tableName()+"."+column.name();
                    String first_matcher = columnStr+"\\("+arg.args()[0]+"\\)";
                    String second_matcher = columnStr+"\\(x\\d+\\)";
                    Pattern pattern1 = Pattern.compile("\\["+first_matcher+"\s"+"="+"\s"+second_matcher+"\\]");
                    Pattern pattern2 = Pattern.compile("\\["+second_matcher+"\s"+"="+"\s"+first_matcher+"\\]");
                    Matcher matcher1 = pattern1.matcher(expr.toString());
                    Matcher matcher2 = pattern2.matcher(expr.toString());
                    while(matcher1.find()) {
                      Pattern pattern = Pattern.compile("x\\d+");
                      Matcher matcher = pattern.matcher(matcher1.group());
                      while(matcher.find()) {
                        if(!Objects.equals(arg.args()[0].toString(), matcher.group())
                                && expr.toString().contains(column.tableName()+"("+matcher.group()+")"))
                          return 0;
                      }
                    }
                    while(matcher2.find()) {
                      Pattern pattern = Pattern.compile("x\\d+");
                      Matcher matcher = pattern.matcher(matcher2.group());
                      while(matcher.find()) {
                        if(!Objects.equals(arg.args()[0].toString(), matcher.group())
                                && expr.toString().contains(column.tableName()+"("+matcher.group()+")"))
                          return 0;
                      }
                    }
                  }
                }
              }
            }
          }
        } else {
          return -1;
        }
      }
      default: return -1; // unknown
    }
  }
}

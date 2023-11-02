package wtune.superopt.logic;

import com.microsoft.z3.Global;
import org.apache.commons.lang3.tuple.Pair;
import wtune.superopt.liastar.*;
import wtune.superopt.substitution.SubstitutionImpl;
import wtune.superopt.uexpr.*;

import java.util.*;

import static wtune.common.utils.IterableSupport.any;
import static wtune.common.utils.ListSupport.filter;
import static wtune.superopt.logic.CASTSupport.schema;
import static wtune.superopt.logic.SqlSolverSupport.hasFreeTuple;
import static wtune.superopt.logic.SqlSolverSupport.overlap;
import static wtune.superopt.uexpr.UExprSupport.isPredOfVarArg;
import static wtune.superopt.uexpr.UExprSupport.mkIsNullPred;
import static wtune.superopt.uexpr.UKind.ADD;
import static wtune.superopt.uexpr.UName.NAME_IS_NULL;


public class SqlSolver {

  public static final Integer timeout = 2000; // ms
  private UExprTranslationResult uExprsResult;
  private UTerm query1;
  private UTerm query2;
  private UVar outVar1;
  private UVar outVar2;

  private int varId = 0;

  public SqlSolver(UExprTranslationResult uExprs) {
    this.uExprsResult = uExprs;
    this.query1 = uExprs.sourceExpr().copy();
    this.query2 = uExprs.targetExpr().copy();
    this.outVar1 = uExprs.sourceOutVar().copy();
    this.outVar2 = uExprs.targetOutVar().copy();
  }

  public SqlSolver(UExprConcreteTranslationResult uExprs) {
    this.uExprsResult = null;
    this.query1 = uExprs.sourceExpr().copy();
    this.query2 = uExprs.targetExpr().copy();
    this.outVar1 = uExprs.sourceOutVar().copy();
    this.outVar2 = uExprs.targetOutVar().copy();
  }

  /* return EQ when q1 == q2 */
  public int proveEq() {
    if (!outVar1.equals(outVar2)) return LogicSupport.NEQ;

    preprocess();
    if (LogicSupport.dumpLiaFormulas) {
      System.out.println("==> Rewritten UExpressions sent to Lia solver: ");
      System.out.println("[[q0]](" + outVar1 + ") := ");
      query1.prettyPrint();
      System.out.println();
      System.out.println("[[q1]](" + outVar2 + ") := ");
      query2.prettyPrint();
      System.out.println();
    }
    UMulImpl.useWeakEquals = true;
    if (query1.equals(query2)) {
      UMulImpl.useWeakEquals = false;
      return LogicSupport.EQ;
    }
    UMulImpl.useWeakEquals = false;
//    if(!needLia(query1, query2)) {
//      uExprsResult.setSrcExpr(query1.copy());
//      uExprsResult.setTgtExpr(query2.copy());
//      try {
//        int result = LogicSupport.proveEqNotNeedLia(uExprsResult);
//        if (result != LogicSupport.UNKNOWN) {
//          return result;
//        } else {
//          System.out.println("exception");
//        }
//      } catch (Exception e) {
//        e.printStackTrace();
//        System.out.println("exception");
//      }
//    }
    SqlSolverSupport translator = new SqlSolverSupport(query1, query2, outVar1);
    Liastar fstar = translator.uexpToLiastar();
    if (LogicSupport.dumpLiaFormulas) {
      System.out.println("==> Lia formula: ");
      System.out.println(fstar);
    }
    Liasolver solver = new Liasolver(fstar);
    // long start = System.currentTimeMillis();
    LiaSolverStatus result = solver.solve();
    // System.out.println(System.currentTimeMillis() - start);
    switch (result) {
      case UNSAT : return LogicSupport.EQ;
      case SAT : return LogicSupport.NEQ;
      default : return LogicSupport.UNKNOWN;
    }
  }

  public static void initialize() {
    Liastar.resetId();
    SemiLinearSet.resetSlsId();
  }

  boolean hasOutSum(UTerm t) {
    switch(t.kind()) {
      case SUMMATION: {
        return true;
      }
      case MULTIPLY:
      case ADD: {
        List<UTerm> subterms = t.subTerms();
        for (UTerm term : subterms) {
          if (hasOutSum(term)) {
            return true;
          }
        }
        return false;
      }
      case PRED: {
        UPred pred = (UPred) t;
        if (pred.isBinaryPred()) {
          return hasOutSum(pred.args().get(0)) || hasOutSum(pred.args().get(1));
        } else  {
          return false;
        }
      }
      default:
        return false;
    }
  }

  boolean needLia(UTerm t1, UTerm t2) {
    return hasOutSum(t1) || hasOutSum(t2);
  }

  HashSet<UVar> decomposeUVar(UVar outVar) {
    HashSet<UVar> result = new HashSet<>();
    if(outVar.kind() == UVar.VarKind.BASE) {
      result.add(outVar.copy());
    } else {
      result.addAll(List.of(outVar.args()));
    }
    return result;
  }

  void preprocess() {
    HashSet<UVar> outerVars = decomposeUVar(outVar1);
    query1 = concretizeBoundedVars(query1.copy(), outerVars);
    query1 = propagateNullValue(query1);
    query1 = propagateConstant(query1, new HashMap<>());
    query1.sortCommAssocItems();
    query2 = concretizeBoundedVars(query2.copy(), outerVars);
    query2 = propagateNullValue(query2);
    query2 = propagateConstant(query2, new HashMap<>());
    query2.sortCommAssocItems();
  }


  public static UTerm propagateConstant(UTerm expr, HashMap<UTerm, Integer> tupleToConst) {
    UKind kind = expr.kind();
    switch (kind) {
      case ADD : {
        ArrayList<UTerm> subterms = new ArrayList<>();
        for(UTerm t : expr.subTerms()) {
          HashMap<UTerm, Integer> tmpBoard = new HashMap<>(tupleToConst);
          tmpBoard.putAll(tupleToConst);
          UTerm tmp = propagateConstant(t, tmpBoard);
          subterms.add(tmp);
        }
        switch(subterms.size()) {
          case 0: assert false; return null;
          case 1: return subterms.get(0);
          default: return UAdd.mk(subterms);
        }
      }
      case MULTIPLY: {
        ArrayList<UTerm> subterms = new ArrayList<>();
        subterms.addAll(expr.subTerms());
        ArrayList<UTerm> newSubTerms = new ArrayList<>();
        int hashMapSize = 0;
        do {
          hashMapSize = tupleToConst.size();
          for (UTerm t : subterms) {
            UTerm tmp = propagateConstant(t, tupleToConst);
            newSubTerms.add(tmp);
          }
          subterms.clear();
          subterms.addAll(newSubTerms);
          newSubTerms.clear();
        } while (hashMapSize != tupleToConst.size());
        switch(subterms.size()) {
          case 0: {
                assert false;
                return null;
          }
          case 1: {
            return subterms.get(0);
          }
          default: {
            if (any(subterms, t -> t.equals(UConst.ZERO)))
              return UConst.zero();
            return UMul.mk(subterms);
          }
        }
      }
      case SUMMATION: {
        USum sum = (USum) expr;
        UTerm body = propagateConstant(((USum)expr).body(), tupleToConst);
        if (body.equals(UConst.ZERO))
          return UConst.zero();
        return USum.mk(sum.boundedVars(), body);
      }
      case NEGATION: {
        HashMap<UTerm, Integer> tmpTupleToConst = new HashMap<>();
        tmpTupleToConst.putAll(tupleToConst);
        UTerm body = propagateConstant(((UNeg)expr).body(), tmpTupleToConst);
        return UNeg.mk(body);
      }
      case SQUASH: {
        UTerm body = propagateConstant(((USquash)expr).body(), tupleToConst);
        return USquash.mk(body);
      }
      case PRED: {
        UPred pred = (UPred) expr.copy();
        if(pred.predKind() == UPred.PredKind.EQ) {
          UTerm left = pred.args().get(0);
          UTerm right = pred.args().get(1);
          if (left instanceof UVarTerm && right instanceof UVarTerm) {
            Integer leftConstVal = tupleToConst.get(left);
            Integer rightConstVal = tupleToConst.get(right);
            if (leftConstVal != null && rightConstVal == null) {
              tupleToConst.put(right, leftConstVal);
              pred.args().set(0, UConst.mk(leftConstVal));
            } else if (leftConstVal == null && rightConstVal != null) {
              tupleToConst.put(left, rightConstVal);
              pred.args().set(1, UConst.mk(rightConstVal));
            }
          } else if (left instanceof UConst && right instanceof UVarTerm) {
            Integer rightConstVal = tupleToConst.get(right);
            if (rightConstVal == null) {
              tupleToConst.put(right, ((UConst) left).value());
            } else if (!rightConstVal.equals(((UConst) left).value())) {
              return UConst.mk(0);
            }
          } else if (left instanceof UVarTerm && right instanceof UConst) {
            Integer leftConstVal = tupleToConst.get(left);
            if (leftConstVal == null) {
              tupleToConst.put(left, ((UConst) right).value());
            } else if (!leftConstVal.equals(((UConst) right).value())) {
              return UConst.mk(0);
            }
          }
          return pred;
        } else {
          return expr;
        }
      }
      default: {
        return expr;
      }
    }
  }

  public static void analyseNullPredicate(UTerm expr, HashSet<UVar> nullTuples, HashSet<UVar> notnullTuples) {
    UKind kind = expr.kind();
    switch (kind) {
      case MULTIPLY: {
        for(UTerm t : expr.subTerms()) {
          analyseNullPredicate(t, nullTuples, notnullTuples);
        }
        return;
      }
      case SUMMATION: {
        analyseNullPredicate(((USum)expr).body(), nullTuples, notnullTuples);
        return;
      }
      case NEGATION: {
        UTerm negBody = ((UNeg) expr).body();
        if(negBody instanceof UPred) {
          UPred pred = (UPred) negBody;
          if (pred.isPredKind(UPred.PredKind.FUNC) && isPredOfVarArg(pred) && pred.predName().equals(NAME_IS_NULL)) {
            final List<UVar> pArgs = UExprSupport.getPredVarArgs(pred);
            assert pArgs.size() == 1;
            notnullTuples.add(pArgs.get(0));
          }
        }
//        else {
//          analyseNullPredicate(negBody, notnullTuples, nullTuples);
//        }
        return;
      }
      case SQUASH: {
        analyseNullPredicate(((USquash)expr).body(), nullTuples, notnullTuples);
        return;
      }
      case PRED: {
        UPred pred = (UPred) expr;
        if (pred.isPredKind(UPred.PredKind.FUNC) && isPredOfVarArg(pred) && pred.predName().equals(NAME_IS_NULL)) {
          final List<UVar> pArgs = UExprSupport.getPredVarArgs(pred);
          assert pArgs.size() == 1;
          nullTuples.add(pArgs.get(0));
        } else if (pred.isPredKind(UPred.PredKind.EQ) && !isPredOfVarArg(pred)) {
          List<UTerm> args = pred.args();
          for(UTerm arg : args) {
            if(arg instanceof UVarTerm) {
              notnullTuples.add(((UVarTerm)arg).var());
            }
          }
        } else if (pred.predKind() != UPred.PredKind.FUNC && pred.predKind() != UPred.PredKind.EQ) {
          List<UTerm> args = pred.args();
          for(UTerm arg : args) {
            if(arg instanceof UVarTerm) {
              notnullTuples.add(((UVarTerm)arg).var());
            }
          }
        }
        return;
      }
      default: {
        return;
      }
    }
  }


  public static void expandNullTuples(HashSet<UVar> nullTuples, ArrayList<HashSet<UVar>> eqPairs) {
    boolean isModified = true;
    while(isModified == true) {
      isModified = false;
      HashSet<UVar> newNullTuples = new HashSet<>();
      for(UVar nullTuple : nullTuples) {
        for (HashSet<UVar> eqTuples : eqPairs) {
          boolean containNullTuple = eqTuples.contains(nullTuple);
          boolean useNullTuple = (nullTuple.kind() == UVar.VarKind.BASE) ? any(eqTuples, arg -> arg.isUsing(nullTuple)) : false;
          if (containNullTuple || useNullTuple) {
            for (UVar v : eqTuples) {
              if (!nullTuples.contains(v)) {
                isModified = true;
                newNullTuples.add(v);
              }
            }
          }
        }
      }
      nullTuples.addAll(newNullTuples);
    }
  }

  public static UTerm propagateNullMultiStep2(UMul expr) {
    ArrayList<UTerm> subterms = new ArrayList<>();
    for(UTerm t : expr.subTerms()) {
      UTerm tmp = propagateNullValue(t);
      if(!tmp.equals(UConst.ZERO)) {
        subterms.add(tmp);
      } else {
        return UConst.zero();
      }
    }
    switch(subterms.size()) {
      case 0: return UConst.zero();
      case 1: return subterms.get(0);
      default: return UMul.mk(subterms);
    }
  }

  public static UTerm propagateNullMultiStep1(UMul expr) {
    HashSet<Pair<UVar, UVar>> eqPairs = collectAllPredicates(expr);
    ArrayList<HashSet<UVar>> eqRels = SqlSolverSupport.buildEqRelation(eqPairs);
    HashSet<UVar> nullTuples = new HashSet<>();
    HashSet<UVar> notnullTuples = new HashSet<>();
    analyseNullPredicate(expr, nullTuples, notnullTuples);
    expandNullTuples(nullTuples, eqRels);
    if(overlap(nullTuples, notnullTuples)) {
      return UConst.zero();
    } else {
      for(UVar nullTuple : nullTuples) {
        if(nullTuple.kind() == UVar.VarKind.BASE) {
          if (any(notnullTuples, arg -> arg.isUsing(nullTuple))) {
            return UConst.zero();
          }
        }
      }
    }
    return expr;
  }

  public static UTerm propagateNullValue(UTerm expr) {
    UKind kind = expr.kind();
    switch (kind) {
      case ADD : {
        ArrayList<UTerm> subterms = new ArrayList<>();
        for(UTerm t : expr.subTerms()) {
          UTerm tmp = propagateNullValue(t);
          if(!tmp.equals(UConst.ZERO)) {
            subterms.add(tmp);
          }
        }
        switch(subterms.size()) {
          case 0: return UConst.zero();
          case 1: return subterms.get(0);
          default: return UAdd.mk(subterms);
        }
      }
      case MULTIPLY: {
        UTerm tmp = propagateNullMultiStep1((UMul) expr);
        if(tmp instanceof UMul) {
          return propagateNullMultiStep2((UMul) tmp);
        } else {
          return tmp;
        }
      }
      case SUMMATION: {
        USum sum = (USum) expr;
        UTerm body = propagateNullValue(((USum)expr).body());
        if(body.equals(UConst.ZERO)) {
          return UConst.zero();
        } else {
          return USum.mk(sum.boundedVars(), body);
        }
      }
      case NEGATION: {
        UTerm body = propagateNullValue(((UNeg)expr).body());
        if(body.equals(UConst.ZERO)) {
          return UConst.one();
        } else {
          return UNeg.mk(body);
        }
      }
      case SQUASH: {
        UTerm body = propagateNullValue(((USquash)expr).body());
        if(body.equals(UConst.ZERO)) {
          return UConst.zero();
        } else {
          return USquash.mk(body);
        }
      }
      case PRED: {
        UPred pred = (UPred) expr;
        if(pred.predKind() == UPred.PredKind.EQ) {
          for(int i = 0; i < pred.args().size(); ++ i) {
            UTerm tmp = propagateNullValue(pred.args().get(i));
            pred.args().set(i, tmp);
          }
          return pred;
        } else {
          return expr;
        }
      }
      default: {
        return expr;
      }
    }
  }


  public static HashSet<Pair<UVar, UVar>> collectAllPredicates(UTerm term) {
    HashSet<Pair<UVar, UVar>> result = new HashSet<>();
    switch(term.kind()) {
      case MULTIPLY: {
        for(UTerm t : term.subTerms()) {
          result.addAll(collectAllPredicates(t));
        }
        return result;
      }
      case SUMMATION: {
        return collectAllPredicates(((USum)term).body());
      }
      case SQUASH: {
        return collectAllPredicates(((USquash)term).body());
      }
      case PRED: {
        final UPred pred = (UPred) term;
        if (pred.isPredKind(UPred.PredKind.EQ) && isPredOfVarArg(pred)) {
          final List<UVar> pArgs = UExprSupport.getPredVarArgs(pred);
          assert pArgs.size() == 2;
          result.add(Pair.of(pArgs.get(0).copy(), pArgs.get(1).copy()));
        }
        return result;
      }
      default: {
        return result;
      }
    }
  }

  public static UVar selectConcreteTuple(ArrayList<HashSet<UVar>> eqRels, UVar boundedVar, HashSet<UVar> outVars) {
    for(HashSet<UVar> eqVars : eqRels) {
      if(eqVars.contains(boundedVar)) {
        for(UVar v : eqVars) {
          if(hasFreeTuple(v, outVars)) {
            return v;
          }
        }
      }
    }
    return null;
  }

  UTerm concretizeBoundedVars(UTerm expr, HashSet<UVar> outerVars) {
    UKind kind = expr.kind();
    switch (kind) {
      case ADD : case MULTIPLY: {
        ArrayList<UTerm> subterms = new ArrayList<>();
        for(UTerm t : expr.subTerms()) {
          subterms.add(concretizeBoundedVars(t, outerVars));
        }
        return (kind == ADD) ? UAdd.mk(subterms) : UMul.mk(subterms);
      }
      case SUMMATION: {
        Set<UVar> boundedVars = ((USum) expr).boundedVars();
        HashSet<UVar> newOuterVars = new HashSet<>(outerVars);
        newOuterVars.addAll(boundedVars);
        UTerm newBody = concretizeBoundedVars(((USum) expr).body(), newOuterVars);
        HashSet<Pair<UVar, UVar>> eqPairs = collectAllPredicates(((USum) expr).body());
        ArrayList<HashSet<UVar>> eqRels = SqlSolverSupport.buildEqRelation(eqPairs);
        HashSet<UVar> newBoundedVars = new HashSet<>();
        for(UVar v : boundedVars) {
          UVar newVar = selectConcreteTuple(eqRels, v, outerVars);
          if(newVar == null) {
            newBoundedVars.add(v);
          } else {
            newBody.replaceVarInplace(v, newVar, false);
          }
        }
        if(newBoundedVars.isEmpty()) {
          return newBody;
        } else {
          return USum.mk(newBoundedVars, newBody);
        }
      }
      case NEGATION: {
        return UNeg.mk(concretizeBoundedVars(((UNeg)expr).body(), outerVars));
      }
      case SQUASH: {
        return USquash.mk(concretizeBoundedVars(((USquash)expr).body(), outerVars));
      }
      default: {
        return expr;
      }
    }
  }

}


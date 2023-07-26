package wtune.superopt.liastar;

import com.microsoft.z3.*;
import wtune.superopt.logic.LogicSupport;
import wtune.superopt.logic.SqlSolver;

import java.util.ArrayList;
import java.util.HashMap;

public class SemiLinearSet {

  ArrayList<LinearSet> sls;

  static private ThreadLocal<Integer> slsId = new ThreadLocal<>() {
    public Integer initialValue() {
      return 0;
    }
  };

  SemiLinearSet() {
    sls = new ArrayList<>();
  }

  static int newSlsId() {
    slsId.set(slsId.get() + 1);
    return slsId.get();
  }

  public static int resetSlsId() {
    slsId.set(0);
    return slsId.get();
  }

  SemiLinearSet(LinearSet ls) {
    sls = new ArrayList<>();
    sls.add(ls);
  }

  public void add(LinearSet ls) {
    sls.add(ls);
  }

  public Liastar tranToLiastar(ArrayList<String> outerVector) {
    Liastar result = null;
    String sumNamePrefix = "sls" + newSlsId();
    for(int i = 0; i < outerVector.size(); ++ i) {
      String varName = outerVector.get(i);
      Liastar sum = Liastar.mkConst(false, 0);
      for(int j = 0; j < sls.size(); ++ j) {
        LinearSet ls = sls.get(j);
        ArrayList<Long> a = ls.a;
//        ArrayList<ArrayList<Long>> b = ls.b;
        String paramNiu = sumNamePrefix + "_niu_" + j;
        long aValue = a.get(i);
        if (aValue == 1) {
          sum = Liastar.mkPlus(false, sum, Liastar.mkVar(false, paramNiu));
        } else if (aValue != 0) {
          sum = Liastar.mkPlus(false, sum,
              Liastar.mkMult(false,
                  Liastar.mkVar(false, paramNiu), Liastar.mkConst(false, aValue)));
        }

//        for(int k = 0; k < b.size(); ++ k) {
//          ArrayList<Long> bk = b.get(k);
//          String paramLambda = sumNamePrefix + "_lambda_" + j + "_" + k;
//          long bkValue = bk.get(i);
//          if (bkValue == 1) {
//            sum = Liastar.mkPlus(false, sum, Liastar.mkVar(false, paramLambda));
//          } else if (bkValue != 0) {
//            sum = Liastar.mkPlus(false, sum,
//                Liastar.mkMult(false,
//                    Liastar.mkVar(false, paramLambda), Liastar.mkConst(false, bkValue)));
//          }
//        }
      }
      result = (result == null) ?
          Liastar.mkEq(false, Liastar.mkVar(false, varName), sum) :
          Liastar.mkAnd(false, result, Liastar.mkEq(false, Liastar.mkVar(false, varName), sum));
    }

    return result;
  }

  public BoolExpr transToSMT(Context ctx, ArrayList<String> innerVector, HashMap<String, IntExpr> varsName, int outerVarNum) {
    if(sls.size() == 0) {
      BoolExpr result = ctx.mkEq(varsName.get(innerVector.get(0)), ctx.mkInt(0));
      for(int i = 1; i < innerVector.size(); ++ i) {
        result = ctx.mkAnd(result, ctx.mkEq(varsName.get(innerVector.get(i)), ctx.mkInt(0)));
      }
      return result;
    }

    HashMap<String, IntExpr> paramName = new HashMap<>();
    BoolExpr bodyExp = ctx.mkTrue();
    ArrayList<Expr> boundVars = new ArrayList<>();

    for(int i = 0; i < sls.size(); ++ i) {
      LinearSet ls = sls.get(i);

      String niuName = "niu_" + i;
      IntExpr niuVar = ctx.mkIntConst(niuName);
      paramName.put(niuName, niuVar);
      boundVars.add(niuVar);
      bodyExp = ctx.mkAnd(bodyExp, ctx.mkLe( ctx.mkInt(0), niuVar));

//      for(int j = 0; j < ls.b.size(); ++ j) {
//        String lambdaName = "lambda_" + i + "_" + j;
//        IntExpr lambdaVar = ctx.mkIntConst(lambdaName);
//        paramName.put(lambdaName, lambdaVar);
//        boundVars.add(lambdaVar);
//        bodyExp = ctx.mkAnd(bodyExp, ctx.mkLe( ctx.mkInt(0), lambdaVar));
//        bodyExp = ctx.mkAnd(bodyExp, ctx.mkImplies(ctx.mkEq(niuVar, ctx.mkInt(0)), ctx.mkEq(lambdaVar, ctx.mkInt(0))));
//      }
    }

    for(int i = 0; i < outerVarNum; ++ i) {
      IntExpr var = varsName.get(innerVector.get(i));
      ArithExpr sum = ctx.mkInt(0);
      for(int j = 0; j < sls.size(); ++ j) {
        LinearSet ls = sls.get(j);

        String niuName = "niu_" + j;
        IntExpr niuVar = paramName.get(niuName);
        long lsValue = ls.a.get(i);
        if(lsValue == 1) {
          sum = ctx.mkAdd(sum, niuVar);
        } else if(lsValue != 0) {
          sum = ctx.mkAdd(sum, ctx.mkMul(niuVar, ctx.mkInt(lsValue)));
        }

//        for(int k = 0; k < ls.b.size(); ++ k) {
//          ArrayList<Long> vec = ls.b.get(k);
//          String lambdaName = "lambda_" + j + "_" + k;
//          IntExpr lambdaVar = paramName.get(lambdaName);
//          long vecValue = vec.get(i);
//          if(vecValue == 1) {
//            sum = ctx.mkAdd(sum, lambdaVar);
//          } else if(vecValue != 0) {
//            sum = ctx.mkAdd(sum, ctx.mkMul(lambdaVar, ctx.mkInt(vecValue)));
//          }
//        }
      }

//      bodyExp = ctx.mkAnd(bodyExp, ctx.mkEq(var, sum));
      bodyExp = ctx.mkOr(bodyExp, ctx.mkNot(ctx.mkEq(var, sum)));
    }

    return ctx.mkForall(boundVars.toArray(new Expr[boundVars.size()]),
        bodyExp, 0, null, null, null, null);
  }

  public LinearSet getGapLS(ArrayList<String> innerVector, Liastar constr, int outerVarNum, int limit) throws Exception {
    try (final Context ctx = new Context()) {
      BoolExpr target = null;
      HashMap<String, IntExpr> varDef = new HashMap<>();
      for (int i = 0; i < innerVector.size(); ++i) {
        String varName = innerVector.get(i);
        IntExpr varExp = ctx.mkIntConst(varName);
        varDef.put(varName, varExp);
        BoolExpr newConstr = ctx.mkLe(ctx.mkInt(0), varExp);
        target = (target == null) ? newConstr : ctx.mkAnd(target, newConstr);
        if(limit > 0) {
          target = ctx.mkAnd(target, ctx.mkLe(varExp, ctx.mkInt(limit)));
        }
      }

      BoolExpr formulaF = (BoolExpr) constr.transToSMT(ctx, varDef);
      BoolExpr formulaSLS = transToSMT(ctx, innerVector, varDef, outerVarNum);
      target = ctx.mkAnd(target, ctx.mkAnd(formulaF, formulaSLS));
      Solver s = ctx.mkSolver(ctx.tryFor(ctx.mkTactic("lia"), SqlSolver.timeout));
      s.add(target);
      Status q = s.check();
      if (q == Status.UNSATISFIABLE)
        return null;
      else if (q == Status.UNKNOWN) {
        if (LogicSupport.dumpLiaFormulas) {
          System.out.println(target);
        }
        throw new Exception("sls fail");
      } else {
        ArrayList<Long> gapVector = new ArrayList<>();
        for (int i = 0; i < outerVarNum; ++i) {
          Long value = Long.parseLong(s.getModel().getConstInterp(varDef.get(innerVector.get(i))).toString());
          gapVector.add(value);
        }
        LinearSet ls = new LinearSet(gapVector, new ArrayList<>());
        return ls;
      }
    }
  }

  public boolean augment(ArrayList<String> innerVector, Liastar constaints, int outerVarNum) throws Exception {
    for(int limit = 1; limit < 10; ++ limit) {
      LinearSet ls = getGapLS(innerVector, constaints, outerVarNum, limit);
      if (ls != null) {
        sls.add(ls);
        return true;
      }
    }

    LinearSet ls = getGapLS(innerVector, constaints, outerVarNum, 0);
    if (ls == null)
      return false;
    else {
      sls.add(ls);
      return true;
    }
  }

  void merge(ArrayList<String> innerVector, Liastar constraints) {
    int lastIndex = sls.size()-1;
    LinearSet ls = sls.get(lastIndex);
    for(int i = 0; i < lastIndex; ++ i) {
      LinearSet cur = sls.get(i);
      if(cur.merge(innerVector, constraints, ls)) {
        sls.remove(lastIndex);
        return;
      }
    }
  }

  void shiftDown(ArrayList<String> innerVector, Liastar constraints) {
    for(int i = 0; i < sls.size(); ++ i)
      sls.get(i).shiftDown(innerVector, constraints);
  }

  void offsetDown(ArrayList<String> innerVector, Liastar constraints) {
    for(int i = 0; i < sls.size(); ++ i)
      sls.get(i).offsetDown(innerVector, constraints);
  }

  public void saturate(ArrayList<String> innerVector, Liastar constraints) {
//    merge(constraints);
//    shiftDown(constraints);
//    offsetDown(constraints);
  }

}


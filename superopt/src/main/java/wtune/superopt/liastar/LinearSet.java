package wtune.superopt.liastar;

import com.microsoft.z3.*;

import java.util.ArrayList;
import java.util.HashMap;

public class LinearSet {

  ArrayList<Long> a;
//  ArrayList<ArrayList<Long>> b;

  LinearSet() {
    a = new ArrayList<>();
//    b = new ArrayList<>();
  }

  LinearSet(ArrayList<Long> x, ArrayList<ArrayList<Long>> y) {
    a = x;
//    b = y;
  }

  public static boolean lessThan(ArrayList<Long> a1, ArrayList<Long> a2) {
    assert a1.size() == a2.size();
    for(int i = 0; i < a1.size(); ++ i) {
      boolean b = ((a1.get(i) <= a2.get(i)) && (a1.get(i) >= 0)) ||
                  ((a1.get(i) >= a2.get(i)) && (a1.get(i) <= 0));
      if(b == false)
        return false;
    }
    return true;
  }

  public static ArrayList<Long> vectorMinus(ArrayList<Long> a1, ArrayList<Long> a2) {
    assert a1.size() == a2.size();
    ArrayList<Long> result = new ArrayList<>();

    for(int i = 0; i < a1.size(); ++ i) {
      result.add(a1.get(i) - a2.get(i));
    }
    return result;
  }

  public boolean merge(ArrayList<String> innerVector, Liastar constraints, LinearSet another) {
    assert false;
    return false;
  }

  public void shiftDown(ArrayList<String> innerVector, Liastar constraints) {
//    int bSize = b.size();
//    for(int i = 0; i < bSize; ++ i) {
//      ArrayList<Long> curVector = b.get(i);
//      if(lessThan(curVector, a)) {
//        HashMap<String, String> cfg = new HashMap<String, String>();
//        cfg.put("model", "true");
//        Context ctx = new Context(cfg);
//        BoolExpr target = ctx.mkTrue();
//        ArrayList<Long> baseVector = vectorMinus(a, curVector);
//
//        HashMap<String, IntExpr> varDef = new HashMap<>();
//        ArrayList<Expr> boundVars = new ArrayList<Expr>();
//        for(int j = 0; j < innerVector.size(); ++ j) {
//          String varName = innerVector.get(j);
//          IntExpr varExp = ctx.mkIntConst(varName);
//          varDef.put(varName, varExp);
//          target = ctx.mkAnd(target, ctx.mkLe( ctx.mkInt(0), varExp));
//
//          for(int k = 0; k < b.size(); ++ k) {
//            String paramName = varName + "_lambda_" + k;
//            IntExpr paramExp = ctx.mkIntConst(paramName);
//            varDef.put(paramName, paramExp);
//            boundVars.add(paramExp);
//          }
//        }
//
//        BoolExpr body = ctx.mkTrue();
//        for(int j = 0; j < innerVector.size(); ++ j) {
//          String varName = innerVector.get(j);
//          IntExpr varExp = varDef.get(varName);
//
//          ArithExpr sum = ctx.mkInt(baseVector.get(j));
//          for(int k = 0; k < b.size(); ++ k) {
//            String paramName = varName + "_lambda_" + k;
//            IntExpr paramExp = varDef.get(paramName);
//            body = ctx.mkAnd(body, ctx.mkLe( ctx.mkInt(0), paramExp));
//
//            ArrayList<Long> curBVecotr = b.get(k);
//            sum = ctx.mkAdd(sum, ctx.mkMul(paramExp, ctx.mkInt(curBVecotr.get(j))));
//          }
//
//          body = ctx.mkAnd(body, ctx.mkEq(varExp, sum));
//        }
//
//        target = ctx.mkAnd(target,
//            ctx.mkNot((BoolExpr) constraints.transToSMT(ctx, varDef)),
//            (BoolExpr) ctx.mkExists(boundVars.toArray(new Expr[boundVars.size()]),
//                body, 0, null, null, null, null)
//        );
//        Solver s = ctx.mkSolver();
//        s.add(target);
//        Status q = s.check();
//        if (q != Status.UNSATISFIABLE) {
//          a = baseVector;
//          return;
//        }
//      }
//    }
  }

  public void offsetDown(ArrayList<String> innerVector, Liastar constraints) {
    assert false;
    return;
  }

}


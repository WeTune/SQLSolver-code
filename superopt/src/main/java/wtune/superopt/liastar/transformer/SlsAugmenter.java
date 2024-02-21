package wtune.superopt.liastar.transformer;

import com.microsoft.z3.*;
import wtune.superopt.liastar.LiaStar;
import wtune.superopt.logic.SqlSolver;

import java.util.*;

import static wtune.common.utils.ListSupport.*;
import static wtune.superopt.liastar.transformer.VectorSupport.*;
import static wtune.superopt.logic.Z3Support.*;

/**
 * An augmenter starts from an empty semi-linear set (SLS) and augments that SLS towards the
 * specified target.
 */
// TODO: coefficient var names have prefix "sls_lambda_" or "sls_lambda1/2/3_";
//  this requires those names are not used in the target LIA formula
public class SlsAugmenter {
  public static final String MSG_SLS_UNKNOWN = "the corresponding SLS is unknown";
  // dimensions of an augmenting vector must not exceed this value
  public static final int AUGMENT_VECTOR_LIMIT = 16;
  // how many times of augmentation are allowed
  public static final int MAX_AUGMENT_TRIES = 64;

  private final SemiLinearSet sls;
  // index of the newly-created/updated linear set in sls, or -1
  private int updatedLSIndex;
  // the name of vector dimensions; useful to check satisfiability
  private final List<String> slsVector;
  // the target to approach
  private final LiaStar target;
  private int augmentTries;

  /**
   * Create an augmenter with a target and a vector of variables that corresponds to dimensions of
   * the SLS.
   *
   * @param slsVector the vector of vars corresponding to SLS dimensions
   * @param target the target
   */
  public SlsAugmenter(List<String> slsVector, LiaStar target) {
    sls = new SemiLinearSet();
    updatedLSIndex = -1;
    this.slsVector = slsVector;
    this.target = target;
    augmentTries = 0;
  }

  /**
   * Find a vector that augments the SLS towards target (i.e. a vector outside SLS but satisfying
   * the target) and add it to the SLS. Return false if there is no such vector.
   */
  public boolean augment() {
    if (augmentTries >= MAX_AUGMENT_TRIES) {
      reportUnknownSls();
    }
    augmentTries++;
    // try to find an augmentation vector
    //System.out.println("start findAugmentation");
    List<Long> augmentation = findAugmentation();
    if (augmentation == null) {
      return false;
    }
    // augment SLS with the vector found
    sls.add(new LinearSet(augmentation, new ArrayList<>()));
    updatedLSIndex = sls.size() - 1;
    //System.out.println("start saturate");
    saturate();
    //System.out.println("end saturate");
    return true;
  }

  public SemiLinearSet sls() {
    return sls;
  }

  private List<Long> findAugmentation() {
    if (findAugmentation(0) == null) {
      return null;
    }
    // try to find an augmentation vector with limited scale
    for (int limit = 1; limit <= AUGMENT_VECTOR_LIMIT; limit <<= 1) {
      List<Long> result = findAugmentation(limit);
      if (result != null) {
        return result;
      }
    }
    // too large vector may cause performance degrade
    reportUnknownSls();
    return null;
  }

  // find a vector satisfying target but not in SLS
  // each dimension of the vector should be <= limit (when limit > 0)
  private List<Long> findAugmentation(int limit) {
    //System.out.println("findAugmentation limit=" + limit);
    try (final Context ctx = new Context()) {
      // construct "target(vector) /\ ~LIA(sls)(vector)"
      // where LIA(sls)(vector) is a LIA formula indicating that vector is in sls
      Map<String, IntExpr> varDef = new HashMap<>();
      BoolExpr nn1 = defineNonNegativeVarsWithLimit(ctx, varDef, slsVector, limit);
      BoolExpr nn2 = defineNonNegativeVars(ctx, varDef, target.collectVarSet());
      BoolExpr targetFormula = (BoolExpr) target.transToSMT(ctx, varDef);
      BoolExpr slsNegFormula = sls.toLiaZ3Neg(ctx, varDef, slsVector);
      BoolExpr toCheck = ctx.mkAnd(nn1, nn2, targetFormula, slsNegFormula);
      // check its satisfiability
      Solver s = ctx.mkSolver(ctx.tryFor(ctx.mkTactic("lia"), SqlSolver.timeout));
      s.add(toCheck);
      Status q = s.check();
      if (q == Status.UNSATISFIABLE) {
        return null;
      }
      if (q == Status.UNKNOWN) {
        reportUnknownSls();
      }
      // satisfiable; get vector from the model
      List<Long> vectorInstance = new ArrayList<>();
      for (String var : slsVector) {
        Long value = Long.parseLong(s.getModel().getConstInterp(varDef.get(var)).toString());
        vectorInstance.add(value);
      }
      return vectorInstance;
    }
  }

  private void reportUnknownSls() {
    throw new RuntimeException(MSG_SLS_UNKNOWN);
  }

  private void saturate() {
    // repeat these operations until convergence
    while (merge() || shiftDown() || offsetDown()) {}
    // convergence
    updatedLSIndex = -1;
  }

  // try to perform a Merge (merge two LS into one)
  // return false if no operation is performed
  private boolean merge() {
    //System.out.println("merge");
    // take the updated LS
    int index1 = updatedLSIndex;
    // traverse each possible pair of linear sets
    for (int index2 = 0, bound = sls.size(); index2 < bound; index2++) {
      // skip the same LS
      if (index1 == index2) {
        continue;
      }
      if (mergeInto(index1, index2) || mergeInto(index2, index1)) {
        return true;
      }
    }
    return false;
  }

  // try to merge LS_index1 into LS_index2
  private boolean mergeInto(int index1, int index2) {
    // for the linear set (shift1, offsets1) and (shift2, offsets2)
    final LinearSet ls1 = sls.get(index1);
    final List<Long> shift1 = ls1.getShift();
    final LinearSet ls2 = sls.get(index2);
    final List<Long> shift2 = ls2.getShift();
    // if shift2 <= shift1
    if (!constLe(shift2, shift1)) {
      return false;
    }
    // check validity of "forall lambda1, lambda2, lambda3.
    // target(shift2 + lambda1 * offsets1
    // + lambda2 * offsets2
    // + lambda3 * (shift1 - shift2))"
    // where "lambda * offsets" means a linear combination of offsets
    // and lambda is the vector of coefficients
    final List<List<Long>> offsets1 = ls1.getOffsets();
    final List<List<Long>> offsets2 = ls2.getOffsets();
    // construct the formula
    List<LiaStar> argVector = constToLia(shift2);
    List<String> lambda1 = createVarVector("sls_lambda1", 0, offsets1.size());
    List<String> lambda2 = createVarVector("sls_lambda2", 0, offsets2.size());
    String lambda3Name = "sls_lambda3";
    LiaStar lambda3 = LiaStar.mkVar(false, lambda3Name);
    List<LiaStar> linearComb1 = linearCombination(nameToLia(lambda1), offsets1, argVector.size());
    List<LiaStar> linearComb2 = linearCombination(nameToLia(lambda2), offsets2, argVector.size());
    List<Long> newOffset = constMinus(shift1, shift2);
    List<LiaStar> product3 = times(constToLia(newOffset), lambda3);
    argVector = plus(argVector, linearComb1);
    argVector = plus(argVector, linearComb2);
    argVector = plus(argVector, product3);
    LiaStar toCheckLia = apply(target, slsVector, argVector);
    Set<String> universalVars = new HashSet<>(lambda1);
    universalVars.addAll(lambda2);
    universalVars.add(lambda3Name);
    // check its validity
    if (isValidLia(toCheckLia, universalVars, false)) {
      // the two linear sets can be merged.
      // merge them into LS(shift2,offsets1+offsets2+{shift1-shift2})
      sls.remove(ls1);
      sls.remove(ls2);
      updatedLSIndex = sls.size();
      List<List<Long>> newOffsets = new ArrayList<>();
      union(newOffsets, offsets1);
      union(newOffsets, offsets2);
      union(newOffsets, newOffset);
      sls.add(new LinearSet(shift2, newOffsets));
      return true;
    }
    return false;
  }

  // try to perform a ShiftDown (decrease shift vector with an offset vector)
  // return false if no operation is performed
  private boolean shiftDown() {
    //System.out.println("shift down");
    // take the updated LS
    int index = updatedLSIndex;
    // for the linear set (shift, offsets) and offset in offsets
    // if offset <= shift
    // check validity of "forall lambda. target(shift - offset + lambda * offsets)"
    // where "lambda * offsets" means a linear combination of offsets
    // and lambda is the vector of coefficients
    final LinearSet ls = sls.get(index);
    final List<Long> shift = ls.getShift();
    final List<List<Long>> offsets = ls.getOffsets();
    for (List<Long> offset : offsets) {
      // we need an offset vector "<=" the shift vector
      if (!constLe(offset, shift)) {
        continue;
      }
      // construct "target(shift - offset + lambda * offsets)"
      List<LiaStar> argVector = constToLia(constMinus(shift, offset));
      List<String> lambda = createVarVector("sls_lambda", 0, offsets.size());
      List<LiaStar> linearComb = linearCombination(nameToLia(lambda), offsets, argVector.size());
      argVector = plus(argVector, linearComb);
      LiaStar toCheckLia = apply(target, slsVector, argVector);
      Set<String> universalVars = new HashSet<>(lambda);
      // check its validity
      if (isValidLia(toCheckLia, universalVars)) {
        // offset is a desired vector
        // replace LS(shift,offsets) with LS(shift-offset,offsets)
        sls.remove(ls);
        updatedLSIndex = sls.size();
        sls.add(new LinearSet(constMinus(shift, offset), offsets));
        return true;
      }
    }
    // no offset vector meets the demand
    return false;
  }

  // try to perform a OffsetDown (decrease offset of a linear set)
  // return false if no operation is performed
  private boolean offsetDown() {
    //System.out.println("offset down");
    // take the updated LS
    int index = updatedLSIndex;
    // for the linear set (shift, offsets) and offset1,offset2 in offsets
    // if offset2 <= offset1
    // check validity of "forall lambda. target(shift + lambda * offsets')"
    // where "lambda * offsets'" means a linear combination of offsets',
    // lambda is the vector of coefficients,
    // and offsets' = offsets \ {offset1} + {offset1-offset2}
    final LinearSet ls = sls.get(index);
    final List<Long> shift = ls.getShift();
    final List<List<Long>> offsets = ls.getOffsets();
    for (int i = 0, bound = offsets.size(); i < bound; i++) {
      for (int j = 0; j < bound; j++) {
        // skip the same offset vector
        if (i == j) {
          continue;
        }
        // offset2 should be "<=" offset1
        final List<Long> offset1 = offsets.get(i);
        final List<Long> offset2 = offsets.get(j);
        if (!constLe(offset2, offset1)) {
          continue;
        }
        // construct "target(shift + lambda * offsets')"
        // where offsets' = offsets \ {offset1} + {offset1-offset2}
        List<List<Long>> offsetsPrime = new ArrayList<>(offsets);
        offsetsPrime.remove(i);
        List<Long> newOffset = constMinus(offset1, offset2);
        if (!offsetsPrime.contains(newOffset)) {
          offsetsPrime.add(newOffset);
        }
        List<String> lambda = createVarVector("sls_lambda", 0, offsetsPrime.size());
        List<LiaStar> linearComb = linearCombination(nameToLia(lambda), offsetsPrime, shift.size());
        List<LiaStar> argVector = plus(constToLia(shift), linearComb);
        LiaStar toCheckLia = apply(target, slsVector, argVector);
        Set<String> universalVars = new HashSet<>(lambda);
        // check its validity
        if (isValidLia(toCheckLia, universalVars)) {
          // (shift,offsets') is the desired linear set
          sls.remove(ls);
          updatedLSIndex = sls.size();
          sls.add(new LinearSet(shift, offsetsPrime));
          return true;
        }
      }
    }
    // no pair of offset vectors meets the demand
    return false;
  }
}

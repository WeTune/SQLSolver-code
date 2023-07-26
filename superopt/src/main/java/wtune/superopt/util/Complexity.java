package wtune.superopt.util;

import wtune.sql.plan.PlanContext;
import wtune.superopt.fragment.Fragment;
import wtune.superopt.fragment.OpKind;

import static wtune.superopt.fragment.OpKind.*;

public interface Complexity extends Comparable<Complexity> {
  int[] opCounts();

  static Complexity mk(Fragment fragment) {
    return new FragmentComplexity(fragment);
  }

  static Complexity mk(PlanContext plan, int nodeId) {
    return new PlanComplexity(plan, nodeId);
  }

  @Override
  default int compareTo(Complexity o) {
    return compareTo(o, true);
  }

  default int compareTo(Complexity other, boolean preferInnerJoin) {
    final int[] opCount0 = opCounts();
    final int[] opCount1 = other.opCounts();

    final int numInput0 = opCount0[INPUT.ordinal()];
    final int numInput1 = opCount1[INPUT.ordinal()];
    if (numInput0 < numInput1) return -1;
    if (numInput0 > numInput1) return 1;

    int result = 0;

    for (int i = 0, bound = opCount0.length; i < bound; i++) {
      // Joins are specially handled. See below.
      if (i < OpKind.values().length && OpKind.values()[i].isJoin()) continue;

      if (result < 0 && opCount0[i] > opCount1[i]) return 0;
      if (result > 0 && opCount0[i] < opCount1[i]) return 0;
      if (opCount0[i] > opCount1[i]) result = 1;
      else if (opCount0[i] < opCount1[i]) result = -1;
    }

    if (result != 0) return result;

    final int numInnerJoin0 = opCount0[INNER_JOIN.ordinal()] + opCount0[CROSS_JOIN.ordinal()];
    final int numOuterJoin0 = opCount0[LEFT_JOIN.ordinal()] + opCount0[RIGHT_JOIN.ordinal()] + opCount0[FULL_JOIN.ordinal()];
    final int numInnerJoin1 = opCount1[INNER_JOIN.ordinal()] + opCount1[CROSS_JOIN.ordinal()];
    final int numOuterJoin1 = opCount1[LEFT_JOIN.ordinal()] + opCount1[RIGHT_JOIN.ordinal()] + opCount1[FULL_JOIN.ordinal()];
    final int numJoin0 = numInnerJoin0 + numOuterJoin0;
    final int numJoin1 = numInnerJoin1 + numOuterJoin1;

    if (numJoin0 < numJoin1) return -1;
    if (numJoin0 > numJoin1) return 1;

    return preferInnerJoin ? Integer.signum(numOuterJoin0 - numOuterJoin1) : 0;
  }
}

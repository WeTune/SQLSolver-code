package wtune.superopt.fragment;

import wtune.superopt.fragment.pruning.*;

import java.util.List;
import java.util.Set;

import static wtune.common.utils.IterableSupport.linearFind;
import static wtune.common.utils.ListSupport.map;
import static wtune.superopt.fragment.OpKind.*;

public class FragmentSupportSPES {
  private static final int DEFAULT_MAX_OPS = 4;
  private static final List<Op> DEFAULT_OP_SET =
      map(List.of(INNER_JOIN, LEFT_JOIN, SIMPLE_FILTER, PROJ, PROJ, IN_SUB_FILTER, UNION, UNION, AGG), Op::mk);
  private static final Set<Rule> DEFAULT_PRUNING_RULES =
      Set.of(
          new MalformedJoin(),
          new MalformedSubquery(),
          new MalformedUnion(),
          new MalformedAgg(),
          new NonLeftDeepJoin(),
          new TooManyJoin(),
          new TooManySubqueryFilter(),
          new TooManySimpleFilter(),
          new TooManyProj(),
          new TooManyUnion(),
          new TooManyAgg(),
          new TooDeepUnion(),
          new TooDeepAgg(),
          // new NotOnRootAgg(),
          new ReorderedFilter(),
          new MeaninglessDedup(),
          new MeaninglessUnionDedup(),
          new DiffUnionInputs());

  static {
    ((Proj) linearFind(DEFAULT_OP_SET, it -> it.kind() == PROJ)).setDeduplicated(true);
    ((Union) linearFind(DEFAULT_OP_SET, it -> it.kind() == UNION)).setDeduplicated(true);
  }

  public static List<Fragment> enumFragmentsSPES() {
    final FragmentEnumerator enumerator = new FragmentEnumerator(DEFAULT_OP_SET, DEFAULT_MAX_OPS);
    enumerator.setPruningRules(DEFAULT_PRUNING_RULES);
    return enumerator.enumerate();
  }
}

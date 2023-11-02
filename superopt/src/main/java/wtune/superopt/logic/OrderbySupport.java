package wtune.superopt.logic;

import wtune.sql.ast.ExprFields;
import wtune.sql.ast.ExprKind;
import wtune.sql.ast.SqlNode;
import wtune.sql.ast.SqlNodeFields;
import wtune.sql.ast.constants.JoinKind;
import wtune.sql.ast.constants.SetOpKind;
import wtune.sql.plan.*;
import wtune.superopt.substitution.*;
import java.util.*;
import java.util.concurrent.atomic.AtomicReference;

import static wtune.common.tree.TreeContext.NO_SUCH_NODE;
import static wtune.common.utils.IterableSupport.zip;
import static wtune.sql.plan.PlanKind.Limit;
import static wtune.sql.plan.PlanKind.valueOf;
import static wtune.sql.plan.PlanSupport.hasNodeOfKind;
import static wtune.sql.plan.PlanSupport.isLiteralEq;

public class OrderbySupport {

  private PlanContext plan0;
  private PlanContext plan1;

  OrderbySupport(PlanContext p0, PlanContext p1) {
    plan0 = p0;
    plan1 = p1;
  }

  public static HashSet<SubstitutionTranslatorResult> sortHandler(PlanContext p0, PlanContext p1) {
    OrderbySupport os = new OrderbySupport(p0, p1);
    return os.trRules();
  }


  boolean isFetchZero(PlanContext p) {
    PlanKind kind = p.kindOf(p.root());
    if (kind == PlanKind.Limit) {
      LimitNode node = (LimitNode) p.nodeAt(p.root());
      return node.limit().template().toString().equals("0");
    }
    return false;
  }


  boolean bothReturnZeroTuples(PlanContext p0, PlanContext p1) {
    boolean isFetchZero0 = isFetchZero(p0);
    boolean isFetchZero1 = isFetchZero(p1);
    return (isFetchZero0 && isFetchZero1);
  }

  public HashSet<SubstitutionTranslatorResult> trRules() {
    try {
      // determine whether both are ordered or both are not ordered
//      System.out.println("OrderBySup\n" + plan0 + "\n" + plan1);

      if (bothReturnZeroTuples(plan0, plan1)) {
        return new HashSet<>();
      }

      deleteUselessLimit(plan0, plan0.root());
      deleteUselessLimit(plan1, plan1.root());
      removeUselessSort(plan0, plan0.root());
      removeUselessSort(plan1, plan1.root());
      if (!cmpOrdered()) {
        return null;
      }
      promoteLimitSort(plan0, plan0.root());
      promoteLimitSort(plan1, plan1.root());
//      System.out.println("Removed Sort\n" + plan0 + "\n" + plan1);

      if (isLiteralEq(plan0, plan1))
        return new HashSet<>();

      mergeLimit(plan0, plan0.root());
      mergeLimit(plan1, plan1.root());

      if (isLiteralEq(plan0, plan1))
        return new HashSet<>();

      HashSet<SubstitutionTranslatorResult> results = new HashSet<>();
      boolean cmpOrderBy = patternMatching(plan0, plan0.root(), plan1, plan1.root(), results);
      if (cmpOrderBy == false) {
        return null;
      } else {
        return results;
      }
    } catch (Exception e) {
      e.printStackTrace();
      return null;
    }
  }

  boolean isOrderByConstant(SortNode sort) {
    for(final Expression expression : sort.sortSpec()) {
      final SqlNode expressionNode = expression.template().$(SqlNodeFields.OrderItem_Expr);
      if(expressionNode == null) continue;
      if(expressionNode.$(SqlNodeFields.Expr_Kind) != ExprKind.Literal) return false;
    }
    return true;
  }

  boolean hasOrderBy(PlanContext p, int nodeId) {
    return hasNodeOfKind(p, PlanKind.Sort) || hasNodeOfKind(p, PlanKind.Limit);
  }

  boolean patternMatching(PlanContext p0, int nodeId0, PlanContext p1, int nodeId1, HashSet<SubstitutionTranslatorResult> results) {
    boolean hasOrderBy0 = hasOrderBy(p0, nodeId0);
    boolean hasOrderBy1 = hasOrderBy(p1, nodeId1);
    if (hasOrderBy0 != hasOrderBy1) {
      return false;
    }
    if (hasOrderBy0 == false) {
      try {
        final SubstitutionTranslatorResult res = SubstitutionSupport.translateAsSubstitution(p0, p1);
        if(res.rule() == null)
          throw new Exception("");
        results.add(res);
        return true;
      } catch (Exception e0) {
        try {
          final SubstitutionTranslatorResult res = SubstitutionSupport.translateAsSubstitution(p1, p0);
          results.add(res);
          return true;
        } catch (Exception e1) {
          return false;
        }
      }
    }

    int sortNodeId0 = findKindNode(p0, nodeId0, PlanKind.Sort);
    int sortNodeId1 = findKindNode(p1, nodeId1, PlanKind.Sort);
    if(sortNodeId0 == NO_SUCH_NODE || sortNodeId1 == NO_SUCH_NODE) return false;
    boolean isSameSort = sameOrderBySemantics(p0, sortNodeId0, p1, sortNodeId1);
    if(!isSameSort) {
      return false;
    }

    PlanContext[] subTree0 = splitPlanContext(p0, sortNodeId0);
    PlanContext[] subTree1 = splitPlanContext(p1, sortNodeId1);
    if(subTree0.length != subTree1.length) {
      return false;
    }
    for(int i = 0; i < subTree0.length; ++ i) {
      PlanContext subPlan0 = subTree0[i];
      PlanContext subPlan1 =  subTree1[i];
      if(subPlan0 == null && subPlan1 == null) break;
      if(subTree0 == null || subPlan1 == null) return false;

      boolean matchingFlag = patternMatching(p0,  subPlan0.root(), p1, subPlan1.root(), results);
      if(matchingFlag == false) {
        return false;
      }
    }
    return true;
  }

  boolean sameOrderBySemantics(PlanContext p0, int sortNodeId0, PlanContext p1, int sortNodeId1) {
    final int parent0 = p0.parentOf(sortNodeId0);
    final int parent1 = p1.parentOf(sortNodeId1);

    final List<Expression> sortSpec0 = ((SortNode)p0.nodeAt(sortNodeId0)).sortSpec();
    final List<Expression> sortSpec1 = ((SortNode)p1.nodeAt(sortNodeId1)).sortSpec();

    final String sortSpec0Str = sortSpec0.toString();
    final String sortSpec1Str = sortSpec1.toString();

    final List<String> sortSpec0Content = new ArrayList<>();
    final List<String> sortSpec1Content = new ArrayList<>();

    if (sortSpec0.size() != sortSpec1.size()) return false;

    for (int i = 0; i < sortSpec0.size(); i++) {
      final Expression sortSpec0Expr = sortSpec0.get(i);
      final Expression sortSpec1Expr = sortSpec1.get(i);

      if (sortSpec0Expr.colRefs().size() != 0) {
        for (final SqlNode colRef : sortSpec0Expr.colRefs()) {
          sortSpec0Content.add(colRef.$(ExprFields.ColRef_ColName).$(SqlNodeFields.ColName_Col).toLowerCase());
        }
      }

      if (sortSpec1Expr.colRefs().size() != 0) {
        for (final SqlNode colRef : sortSpec1Expr.colRefs()) {
          sortSpec1Content.add(colRef.$(ExprFields.ColRef_ColName).$(SqlNodeFields.ColName_Col).toLowerCase());
        }
      }
    }

    if(parent0 == NO_SUCH_NODE && parent1 == NO_SUCH_NODE){
      return sortSpec0Str.equals(sortSpec1Str);
    }
    return sortSpec0Str.equals(sortSpec1Str)
            && sortSpec0Content.equals(sortSpec1Content)
            && new PlanEq(p0, p1).isSemanticEqForNodes(parent0, parent1);
  }

  int findKindNode(PlanContext plan, int nodeId, PlanKind k) {
    if (plan.kindOf(nodeId) == k) return nodeId;
    final int numChildren = plan.nodeAt(nodeId).numChildren(plan);
    final int[] children = plan.childrenOf(nodeId);
    assert numChildren <= children.length;
    for (int i = 0; i < numChildren; ++i) {
      int tmpId = findKindNode(plan, children[i], k);
      if(tmpId != NO_SUCH_NODE) {
        return tmpId;
      }
    }
    return NO_SUCH_NODE;
  }

  PlanContext[] splitPlanContext(PlanContext plan, int nodeId) {
    final int rootId = plan.root();
    final PlanKind kind = plan.kindOf(nodeId);
    final PlanNode cur = plan.nodeAt(nodeId);
    int numChildren = plan.nodeAt(nodeId).numChildren(plan);
    int[] children = plan.childrenOf(nodeId);
    assert numChildren <= children.length;
    PlanContext[] results = new PlanContext[2];
    results[0] = null;
    results[1] = null;

    if(nodeId == rootId) {
      plan.myDeleteNode(rootId);
      plan.setRoot(children[0]);
      results[0] = plan;
      return results;
    } else if((plan.parentOf(nodeId) == rootId) && (plan.kindOf(rootId) == Limit)) {
      plan.myDeleteNode(nodeId);
      plan.myDeleteNode(rootId);
      plan.setRoot(children[0]);
      results[0] = plan;
      return results;
    } else {
      assert false;
      return results;
    }

    /*
    final PlanNode limit = cur.parent(plan);
    final int limitId = plan.parentOf(nodeId);
    final PlanKind limitKind = limit.kind();
    assert  limitKind == Limit;
    if(limitId == rootId) {
      plan.myDeleteNode(limitId);
      plan.setRoot(nodeId);
      plan.myDeleteNode(nodeId);
      plan.setRoot(children[0]);
      results[0] = plan;
      return results;
    }

    results[0] = plan.copy();
    results[0].deleteNode(limitId);
    results[0].deleteNode(nodeId);

    results[1] = plan.copy();
    results[1].setRoot(children[0]);
    results[1].deleteNode(limitId);
    results[1].deleteNode(nodeId);

    return results;
     */
  }

  boolean isUnion(PlanKind kind, PlanNode node) {
    if(kind == PlanKind.SetOp) {
      return ((SetOpNode)node).opKind() == SetOpKind.UNION;
    } else {
      return false;
    }
  }

  boolean isLeftJoin(PlanKind kind, PlanNode node) {
    if(kind == PlanKind.Join) {
      return (((JoinNode)node).joinKind() == JoinKind.LEFT_JOIN);
    } else {
      return false;
    }
  }

  boolean isUnionLeftJoin(PlanKind kind, PlanNode node) {
    return isUnion(kind, node) || isLeftJoin(kind, node);
  }

  int[] getParentSortParams(PlanContext plan, int nodeId) {
    if(nodeId == NO_SUCH_NODE) {
      return null;
    }
    final PlanNode node = plan.nodeAt(nodeId);
    final PlanKind nodeKind = node.kind();
    if(nodeKind == PlanKind.Sort) {
      int[] result = new int[3];
      final int sortId = nodeId;
      result[0] = sortId;
      final int limitId = plan.parentOf(sortId);
      if(limitId == NO_SUCH_NODE) {
        result[1] = 0;
        result[2] = -1;
        return result;
      }
      final PlanNode limitnode = plan.nodeAt(limitId);
      final PlanKind limitKind = limitnode.kind();
      if(limitKind != Limit) {
        result[1] = 0;
        result[2] = -1;
        return result;
      }
      return limitMetaInfo(limitnode, sortId);
    } else if(nodeKind == PlanKind.Proj) {
      return getParentSortParams(plan, plan.parentOf(nodeId));
    } else {
      return null;
    }
  }

  int findBiggerLimit(PlanContext plan, int nodeId, int sourceId) {
    final PlanNode source = plan.nodeAt(sourceId);
    final PlanKind sourceKind = source.kind();
    assert sourceKind == Limit;
    if(nodeId == NO_SUCH_NODE) return -1;
    if(nodeId != sourceId) {
      int numChildren = plan.nodeAt(nodeId).numChildren(plan);
      if(numChildren != 1) return -1;
      final PlanNode node = plan.nodeAt(nodeId);
      final PlanKind nodeKind = node.kind();
      if(nodeKind == Limit) {
        Expression nodeOffset = ((LimitNode)node).offset();
        Expression nodeLimit =  ((LimitNode)node).limit();
        Expression sourceOffset = ((LimitNode)source).offset();
        Expression sourceLimit = ((LimitNode)source).limit();
        if(nodeOffset != null || sourceOffset != null) return -1;
        if(Integer.parseInt(nodeLimit.toString()) >= Integer.parseInt(sourceLimit.toString())) return nodeId;
      }
    }
    return findBiggerLimit(plan, plan.parentOf(nodeId), sourceId);

  }

  int[] limitMetaInfo(PlanNode limitNode, int sortNodeId) {
    int[] result = new int[3];
    result[0] = sortNodeId;
    Expression offset = ((LimitNode)limitNode).offset();
    result[1] = offset == null ? 0 : Integer.parseInt(offset.toString());
    Expression limit =  ((LimitNode)limitNode).limit();
    result[2] = limit == null ? -1 : Integer.parseInt(limit.toString());
    return result;
  }

  int[] getChildSortParams(PlanContext plan, int nodeId) {
    if(nodeId == NO_SUCH_NODE) {
      return null;
    }
    PlanNode node = plan.nodeAt(nodeId);
    PlanKind kind = node.kind();
    if(kind == Limit) {
      return limitMetaInfo(node, plan.childOf(nodeId, 0));
    } else if(kind == PlanKind.Sort) {
      int[] result = new int[3];
      result[0] = nodeId;
      result[1] = 0;
      result[2] = -1;
      return result;
    } else if(kind == PlanKind.Proj) {
      return getChildSortParams(plan, plan.childOf(nodeId, 0));
    } else {
      return null;
    }
  }


  boolean canMergeSortLimit(PlanContext plan, int[] childParams, int[] parentParams) {
    if(childParams == null || parentParams == null)
      return false;

    if(childParams.length != 3 || parentParams.length != 3)
      return false;

    return (childParams[1] == parentParams[1]) && (childParams[2] == parentParams[2]);
  }

  void deleteSortLimit(PlanContext plan, int sortId) {
    if(plan.kindOf(plan.parentOf(sortId)) == Limit) {
      plan.myDeleteNode(plan.parentOf(sortId));
    }
    plan.myDeleteNode(sortId);
  }

  void mergeLimit(PlanContext plan, int nodeId) {
    if(nodeId == 0) return;

    final int rootId = plan.root();
    final PlanKind kind = plan.kindOf(nodeId);
    final PlanNode cur = plan.nodeAt(nodeId);
    int numChildren = plan.nodeAt(nodeId).numChildren(plan);
    int[] children = plan.childrenOf(nodeId);
    assert numChildren <= children.length;

    if((rootId != nodeId) && isUnionLeftJoin(kind, cur)) {
      int[] upperLimitParams = getParentSortParams(plan, plan.parentOf(nodeId));
      if (upperLimitParams != null) {
        if(isUnion(kind, cur)) {
          boolean canMergeLimit = true;
          int[][] childrenSortParams = new int[numChildren][3];
          for (int i = 0; i < numChildren; ++i) {
            final int childId = children[i];
            if(childId == NO_SUCH_NODE) {
              continue;
            }
            int[] childSortParams = getChildSortParams(plan, childId);
            if(childSortParams == null) {
              canMergeLimit = false;
              break;
            }
            childrenSortParams[i][0] = childSortParams[0];
            childrenSortParams[i][1] = childSortParams[1];
            childrenSortParams[i][2] = childSortParams[2];
            canMergeLimit = canMergeLimit & canMergeSortLimit(plan, childSortParams, upperLimitParams);
          }
          if(canMergeLimit) {
            for(int i = 0; i <numChildren; ++ i) {
              final int sortId = childrenSortParams[i][0];
              deleteSortLimit(plan, sortId);
            }
          }
        } else {
          final int childId = children[0];
          if (childId != NO_SUCH_NODE) {
            int[] childSortParams = getChildSortParams(plan, childId);
            if(canMergeSortLimit(plan, childSortParams, upperLimitParams)) {
              final int sortId = childSortParams[0];
              deleteSortLimit(plan, sortId);
            }
          }
        }
      }
    }

    if(rootId != nodeId) {
      if(kind == Limit) {
        int deleteId = findBiggerLimit(plan, nodeId, nodeId);
        if(deleteId != -1) {
          if(deleteId == rootId) {
            int numDeleteChildren = plan.nodeAt(deleteId).numChildren(plan);
            int[] deleteChildren = plan.childrenOf(deleteId);
            assert numDeleteChildren == 1;
            plan.setRoot(deleteChildren[0]);
          }
          plan.deleteNode(deleteId);
        }
      }
    }

    for (int i = 0; i < numChildren; ++i) {
      if(children[i] != 0) {
        mergeLimit(plan, children[i]);
      }
    }
  }

  void deleteUselessLimit(PlanContext plan, int nodeId) {
    if(nodeId == 0) return;

    final int rootId = plan.root();
    final PlanKind kind = plan.kindOf(nodeId);
    final PlanNode cur = plan.nodeAt(nodeId);
    int numChildren = plan.nodeAt(nodeId).numChildren(plan);
    int[] children = plan.childrenOf(nodeId);
    assert numChildren <= children.length;

    if(rootId != nodeId) {
      if(kind == Limit) {
        int deleteId = findBiggerLimit(plan, nodeId, nodeId);
        if(deleteId != -1) {
          if(deleteId == rootId) {
            int numDeleteChildren = plan.nodeAt(deleteId).numChildren(plan);
            int[] deleteChildren = plan.childrenOf(deleteId);
            assert numDeleteChildren == 1;
            plan.setRoot(deleteChildren[0]);
          }
          plan.deleteNode(deleteId);
        }
      }
    }

    for (int i = 0; i < numChildren; ++i) {
      if(children[i] != 0) {
        deleteUselessLimit(plan, children[i]);
      }
    }
  }

  void promoteLimitSort(PlanContext plan, int nodeId) {
    if (nodeId == NO_SUCH_NODE) {
      return;
    }

    final PlanKind kind = plan.kindOf(nodeId);
    int numChildren = plan.nodeAt(nodeId).numChildren(plan);
    int[] children = plan.childrenOf(nodeId);
    assert numChildren <= children.length;
    for (int i = 0; i < numChildren; ++i) {
      if(children[i] != NO_SUCH_NODE) {
        promoteLimitSort(plan, children[i]);
      }
    }
    if (kind != PlanKind.Sort) {
      return;
    }
    int limitId = plan.parentOf(nodeId);
    if (limitId == NO_SUCH_NODE) {
      return;
    }
    PlanKind limitKind = plan.kindOf(limitId);
    if (limitKind != Limit) {
      return;
    }
    int[] upperSortParams = getParentSortParams(plan, plan.parentOf(limitId));
    if (upperSortParams == null) {
      return;
    }
    if (upperSortParams[1] == 0 && upperSortParams[2] == -1) {
      // Assume LIMIT has offset or limit parameters
      plan.myDeleteNode(nodeId);
      LimitNode limitNode = (LimitNode) plan.nodeAt(limitId);
      PlanNode newLimitNode = new LimitNodeImpl(limitNode.limit(), limitNode.offset());
      int newLimitId = plan.bindNode(newLimitNode);
      plan.myDeleteNode(limitId);
      plan.setChild(newLimitId, 0, upperSortParams[0]);
      if (upperSortParams[0] == plan.root()) {
        plan.setRoot(newLimitId);
      }
    }
  }

  void removeUselessSort(PlanContext plan, int nodeId) {
    if(nodeId == 0) return;

    final int rootId = plan.root();
    final PlanKind kind = plan.kindOf(nodeId);
    final PlanNode cur = plan.nodeAt(nodeId);
    int numChildren = plan.nodeAt(nodeId).numChildren(plan);
    int[] children = plan.childrenOf(nodeId);
    assert numChildren <= children.length;

    if (kind == PlanKind.Sort){
//      System.out.println(PlanSupport.stringifyNode(plan, nodeId));
      if (nodeId != rootId) {
        final PlanNode parent = cur.parent(plan);
        if (parent.kind() != Limit) {
          plan.myDeleteNode(nodeId);
        }
      }
      else if ((((SortNode) cur).indexedRefs().length == 0 && isOrderByConstant((SortNode) cur)) ||
              (plan.kindOf(plan.childOf(nodeId, 0)) == PlanKind.Proj && PlanSupport.stringifyNode(plan, nodeId).contains("null"))){
        int newRoot = plan.childOf(rootId, 0);
        plan.myDeleteNode(nodeId);
        plan.setRoot(newRoot);
      }else {
        try {
          ((SortNode) cur).sortSpec().forEach(e -> {
                    if (e.toString().contains("'")){
                      ((SortNode) cur).sortSpec().remove(e);
                      throw new Error();
                    }
                  });
        }catch (Error e){
        }
      }
    }

    for (int i = 0; i < numChildren; ++i) {
      if(children[i] != 0) {
        removeUselessSort(plan, children[i]);
      }
    }
  }

  boolean cmpOrdered() {
    boolean isOrdered0 = isOrderedPlan(plan0);
    boolean isOrdered1 = isOrderedPlan(plan1);
    return (isOrdered0 == isOrdered1);
  }

  boolean isOrderedPlan(PlanContext p) {
    PlanKind kind = p.kindOf(p.root());
    return (kind == PlanKind.Sort) || (kind == PlanKind.Limit);
  }

}

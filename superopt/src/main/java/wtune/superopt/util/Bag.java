package wtune.superopt.util;

import java.util.HashMap;
import java.util.Map;


public class Bag<T> {

  private final Map<T, Integer> countMap;

  public Bag() {
    countMap = new HashMap<>();
  }

  public void add(T e, int count) {
    if (countMap.containsKey(e)) countMap.compute(e, (k, v) -> v + count);
    else countMap.put(e, count);
  }

  public void add(T e) {
    add(e, 1);
  }

  public int count(T e) {
    return countMap.getOrDefault(e, 0);
  }

  public int size() {
    return countMap.values().stream().mapToInt(Integer::intValue).sum();
  }

  public static <T> Bag<T> minus(Bag<T> bag1, Bag<T> bag2) {
    Bag<T> diffBag = new Bag<>();
    for (T key : bag1.countMap.keySet()) {
      diffBag.add(key, Math.max(bag1.count(key) - bag2.count(key), 0));
    }
    return diffBag;
  }

}
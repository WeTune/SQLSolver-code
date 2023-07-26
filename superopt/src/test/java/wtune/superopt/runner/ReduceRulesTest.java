package wtune.superopt.runner;

import org.junit.jupiter.api.Test;
import wtune.common.utils.IOSupport;
import wtune.superopt.substitution.Substitution;
import wtune.superopt.substitution.SubstitutionBank;
import wtune.superopt.substitution.SubstitutionSupport;

import java.io.IOException;
import java.io.PrintWriter;

import static org.junit.jupiter.api.Assertions.*;
import static wtune.superopt.runner.RunnerSupport.dataDir;

class ReduceRulesTest {

  @Test
  void testRun() throws IOException {
    final var inFile = dataDir().resolve("prepared/rules.test.txt");
    final SubstitutionBank bank = SubstitutionSupport.loadBank(inFile);
    SubstitutionBank reducedBank = bank;
    int pass = 1;
    while (true) {
      final int oldSize = reducedBank.size();
      reducedBank = SubstitutionSupport.reduceBank(reducedBank);
      final int minSize = reducedBank.size();

      System.out.printf("Pass %d: %d -> %d\n", pass++, oldSize, minSize);
      if (minSize == oldSize) break;
    }
  }
}
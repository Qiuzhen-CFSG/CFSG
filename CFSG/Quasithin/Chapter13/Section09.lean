module

public import CFSG.Quasithin.Chapter13.Section09.Elementary
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth
public import CFSG.Quasithin.Chapter13.Section09.TerminalObstruction

public import CFSG.Quasithin.Chapter13.Section09.Source

/-!
# The original wreath exclusion, Theorem 13.9.1

Aschbacher--Smith Theorem 13.9.1 (combined manuscript of 1 March 2004,
printed pp.969--974) excludes S₄ wr C₂ as a maximal two-local containing
a Sylow two-subgroup in a simple QTKE group.

`source13_9_1` proves the full original configuration impossible.
The centralizer growth, quaternion core, S₅ normalizer action, marked
centralizer splitting and terminal PSL₃(2) subgroup are constructed from
the original hypotheses. Two actual cubic actions with complementary
supports on B give the final contradiction 9 ∣ 1920, avoiding the incorrect
printed Delta5 product assertion. Existing conditional interfaces remain
available, but no such premise occurs in the final source theorem.
-/

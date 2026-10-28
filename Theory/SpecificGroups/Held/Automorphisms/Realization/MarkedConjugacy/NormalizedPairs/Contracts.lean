module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.Conditions
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedSubgroup

/-!
# The remaining involution calculations for normalized Held pairs

The explicit second seed is `(ab³)⁴` in the retained ATLAS carrier. The two
contracts below specify coverage of all involutions by its conjugacy
class and that of `a`, and the marked fixed-point test on those actual classes
for exponents 1 and 3. These are mathematical contracts, not assumed theorems.
The assembly in `NormalizedPairs` discharges the other fifteen exponents by
an explicit power-doubling conjugation, including rejection of exponent zero.

Source: `Model/Source/HeG1-P1.M`, its seven uncommented relations and its
literal subgroup `M1`. The second seed and the two reduced exponents come
from computation in `Model/Source/HeG1-p2058B0.g1` and `.g2`.
-/

namespace Held.Realization.MarkedConjugacy.NormalizedPairs

/-- The second involution seed in the original ATLAS generators. -/
@[expose] public def secondSeed : He := (a * b ^ 3) ^ 4

/-- Coverage is a separate obligation: every actual involution belongs to
one of the two displayed conjugacy classes. -/
@[expose] public def InvolutionCoverage : Prop :=
  ∀ x : He, orderOf x = 2 → IsConj a x ∨ IsConj secondSeed x

/-- A fixed-point calculation on an entire actual conjugacy class. The
restriction to exponents 1 and 3 is justified by `NormalizedPairs`, and does
not assert completeness of any externally enumerated list. -/
@[expose] public def ClassCalculation (seed : He) : Prop :=
  ∀ k : Fin 17, k = 1 ∨ k = 3 → ∀ x : He, IsConj seed x →
    (∀ i : Fin 7, relationWord x (x * (a * b) ^ k.val) i = 1) →
    ∃ p : Fin 2058, PairFixes x (x * (a * b) ^ k.val) p

end Held.Realization.MarkedConjugacy.NormalizedPairs

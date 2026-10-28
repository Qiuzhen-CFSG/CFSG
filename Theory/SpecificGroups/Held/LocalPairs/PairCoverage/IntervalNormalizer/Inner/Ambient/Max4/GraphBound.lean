module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound.Row0
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound.Row1
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound.Row2
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound.Row3
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound.Row4
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound.Row5
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound.Row6
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound.Odd

/-!
# Bounds for the seven even colored Held graph groups

The literal color tables in `Max4.Data`, combined with graph adjacency to
vertices 0, 1, 2, 3 and invariant neighbor counts give full-group bounds
3072, 3072, 1024, 2048, 3072, 1024, 1024. The graph's four-point stabilizer
is trivial. In row 3 an explicitly checked odd colored symmetry halves the
bound. Every finite computation is kernel checked.

This is independent of the identification of the colors with actual orbit
cardinalities. It provides precisely the graph input to the max4 interval
normalizer calculation for GLS3 Table 5.3p, using the unchanged ATLAS
HeG1-p2058B0/max4 data. See `GraphBound/Source/README.md` for reproduction.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4
open GraphBound

/-- The seven even colored graph groups satisfy their stated bounds,
without any orbit, ambient-order, or automorphism-normalizer premise. -/
public theorem evenColoredGraphGroup_card_le (j : Fin 7) :
    Nat.card (evenColoredGraphGroup j) ≤ bound j := by
  fin_cases j
  · change Nat.card (evenColoredGraphGroup 0) ≤ 3072
    exact (even_card_le 0).trans full_card0
  · change Nat.card (evenColoredGraphGroup 1) ≤ 3072
    exact (even_card_le 1).trans full_card1
  · change Nat.card (evenColoredGraphGroup 2) ≤ 1024
    exact (even_card_le 2).trans full_card2
  · change Nat.card (evenColoredGraphGroup 3) ≤ 1024
    apply even_card_le_of_odd 3 full_card3 oddPermutation odd_mem
    rw [odd_sign]
    decide
  · change Nat.card (evenColoredGraphGroup 4) ≤ 3072
    exact (even_card_le 4).trans full_card4
  · change Nat.card (evenColoredGraphGroup 5) ≤ 1024
    exact (even_card_le 5).trans full_card5
  · change Nat.card (evenColoredGraphGroup 6) ≤ 1024
    exact (even_card_le 6).trans full_card6

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4

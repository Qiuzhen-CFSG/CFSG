module
public import Theory.GroupTheory.Recognition.Brauer.FixedFactors
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Sizes of Brauer's point and line blocks

In Brauer, *On finite Desarguesian planes I*, p. 119 after (2.5), each
point and each line consists of `q²` involutions. This module proves the
cardinality assertion for the original conjugate-coset subsets and proves
`1 < q`. The involution assertion is supplied by `BlockIntersection`.

Multiplication by `j` and conjugation are bijections, so the block sizes
are the orders of `M` and `Mstar`. The fixed-factor decomposition gives
both orders as `q²`. Finally postulate (II), `Mstar ≠ 1`, makes this square
strictly greater than one and hence gives `q > 1`. No projective-plane
postulate or geometric counting formula is assumed.
-/

open scoped Pointwise

namespace Theory.GroupTheory.BrauerPlaneSeed

/-- Brauer I, p. 119: both block families have size `q²`, with `q > 1`. -/
public theorem block_sizes {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G) :
    (∀ p : S.Point, (p : Set G).ncard = S.q ^ 2) ∧
    (∀ l : S.Line, (l : Set G).ncard = S.q ^ 2) ∧ 1 < S.q := by
  obtain ⟨_, _, _, _, _, _, _, _, hM, hMstar⟩ := S.fixed_factors
  refine ⟨?_, ?_, ?_⟩
  · intro p
    obtain ⟨g, hg⟩ := p.property
    rw [← hg, Set.ncard_smul_set, BrauerPlaneSeed.basePoint, Set.ncard_smul_set]
    exact hM
  · intro l
    obtain ⟨g, hg⟩ := l.property
    rw [← hg, Set.ncard_smul_set, BrauerPlaneSeed.baseLine, Set.ncard_smul_set]
    exact hMstar
  · have hlarge : 1 < S.q ^ 2 := by
      rw [← hMstar]
      exact S.Mstar.one_lt_card_iff_ne_bot.mpr S.Mstar_ne_bot
    by_contra hq
    have hle : S.q ≤ 1 := Nat.le_of_not_gt hq
    have : S.q ^ 2 ≤ 1 := by simpa only [one_pow] using Nat.pow_le_pow_left hle 2
    exact (not_lt_of_ge this) hlarge

end Theory.GroupTheory.BrauerPlaneSeed

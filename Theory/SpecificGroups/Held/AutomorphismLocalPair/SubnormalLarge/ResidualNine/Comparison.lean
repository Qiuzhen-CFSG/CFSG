module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine.Definitions
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine.Comparison.Centralizer
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine.Comparison.Containment
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders

/-!
# The full Held seed normalizer is the conjugated pure pair

The full normalizer has order at most 9216 because it normalizes the seed's
ambient centralizer, identified with catalogue row 12. Explicit conjugation
identities place the pure pair, conjugated by the inverse marked word, inside
that full normalizer. The independently certified order of the pair is 9216,
so containment is equality. Transport back uses Lean's conjugation convention
`x ↦ g*x*g⁻¹`.

This is the literal subgroup comparison required by the residual-nine quotient
calculation. No simplicity, total Held order, or local-structure hypothesis
is used. Source: GLS3 Table 5.3p and Aschbacher--Smith, printed p.526.
-/

public section
namespace Held.AutomorphismLocalPair.ResidualNine
open Subgroup LocalPairs.PairCoverage.LocalActions.Exhaustion

/-- The full normalizer of the join of both E64 seeds maps onto the unchanged
pure pair under the published ambient conjugation. -/
theorem representative_map_pairConjugator :
    representativeLargeLocal.map (MulAut.conj pairConjugator).toMonoidHom =
      candidateProduct false 0 := by
  have hle : candidateProduct false 0 ≤
      representativeLargeLocal.map (MulAut.conj pairConjugator).toMonoidHom := by
    intro x hx
    refine ⟨_, Comparison.candidate_map_inverse_le (mem_map_of_mem _ hx), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  apply (eq_of_le_of_card_ge hle ?_).symm
  calc
    Nat.card (representativeLargeLocal.map (MulAut.conj pairConjugator).toMonoidHom) =
        Nat.card representativeLargeLocal :=
      card_map_of_injective (MulAut.conj pairConjugator).injective
    _ ≤ 9216 := Comparison.representativeLargeLocal_card_le
    _ = Nat.card (candidateProduct false 0) := ((candidateOrders false 0).2.2).symm

end Held.AutomorphismLocalPair.ResidualNine

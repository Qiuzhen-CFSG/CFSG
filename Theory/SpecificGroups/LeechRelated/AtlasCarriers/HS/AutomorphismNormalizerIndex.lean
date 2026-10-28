module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.Graph
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.GraphNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.GraphOrder
import Lean.Elab.Tactic.Omega

/-!
# The HS permutation-normalizer index divides two

The exact ATLAS carrier has order 44,352,000. Its permutation normalizer
preserves the explicit orbital graph, whose full automorphism group has
order at most 88,704,000. The subgroup order formula therefore forces the
relative index of the carrier in its normalizer to be one or two.

`CarrierOrder`, `GraphNormalizer` and `GraphOrder` prove these three inputs
for the permutations defining `HS.generated`, with all finite witnesses
checked in Lean's kernel. The conditional reductions are retained, and
`normalizer_relIndex_dvd_two_pow` discharges every counting and graph premise.
This establishes the normalizer part of the outer entry in GLS3, Table 5.3m,
printed p.274. The separate automorphism-coverage input belongs to
`AutomorphismNormalizer.lean`.

The relative index is that of H inside N(H), not the ambient symmetric
group index. No simplicity or perfectness assumption is used in this step.
-/

public section
namespace Sporadic.LeechRelated.HS
open Subgroup

/-- The exact carrier order turns the proposed normalizer bound into index at most two. -/
theorem normalizer_relIndex_dvd_two_of_card_le
    (hc : Nat.card (normalizer (generated : Set (Equiv.Perm (Fin 100)))) ≤ 88704000) :
    generated.relIndex (normalizer (generated : Set (Equiv.Perm (Fin 100)))) ∣ 2 := by
  let N := normalizer (generated : Set (Equiv.Perm (Fin 100)))
  have he := relIndex_mul_relIndex (⊥ : Subgroup (Equiv.Perm (Fin 100))) generated N
    bot_le generated.le_normalizer
  simp only [relIndex_bot_left] at he
  change Nat.card Carrier * generated.relIndex N = Nat.card N at he
  rw [NormalizerIndex.card_carrier] at he
  change Nat.card N ≤ 88704000 at hc
  have hp : 0 < Nat.card N := Nat.card_pos
  have h : generated.relIndex N = 1 ∨ generated.relIndex N = 2 := by
    omega
  change generated.relIndex N ∣ 2
  rcases h with h | h <;> simp [h]

/-- The two independent graph calculations suffice for the actual normalizer index. -/
theorem normalizer_relIndex_dvd_two_of_graph_bound
    (hn : normalizer (generated : Set (Equiv.Perm (Fin 100))) ≤ NormalizerIndex.graphGroup)
    (hc : Nat.card NormalizerIndex.graphGroup ≤ 88704000) :
    generated.relIndex (normalizer (generated : Set (Equiv.Perm (Fin 100)))) ∣ 2 :=
  normalizer_relIndex_dvd_two_of_card_le ((Subgroup.card_le_of_le hn).trans hc)

/-- Conditional assembly in precisely the form consumed by the outer-quotient proof. -/
theorem normalizer_relIndex_dvd_two_pow_of_graph_bound
    (hn : normalizer (generated : Set (Equiv.Perm (Fin 100))) ≤ NormalizerIndex.graphGroup)
    (hc : Nat.card NormalizerIndex.graphGroup ≤ 88704000) :
    ∃ n : ℕ,
      generated.relIndex (normalizer (generated : Set (Equiv.Perm (Fin 100)))) ∣ 2 ^ n := by
  exact ⟨1, by simpa using normalizer_relIndex_dvd_two_of_graph_bound hn hc⟩

/-- The index of the defining HS subgroup in its actual permutation normalizer
divides two. -/
theorem normalizer_relIndex_dvd_two :
    generated.relIndex (normalizer (generated : Set (Equiv.Perm (Fin 100)))) ∣ 2 :=
  normalizer_relIndex_dvd_two_of_graph_bound
    NormalizerIndex.normalizer_le_graphGroup NormalizerIndex.graphGroup_card_le

/-- The unconditional normalizer-index bound in the form consumed by the
outer-quotient argument. The exponent is one. -/
theorem normalizer_relIndex_dvd_two_pow :
    ∃ n : ℕ,
      generated.relIndex (normalizer (generated : Set (Equiv.Perm (Fin 100)))) ∣ 2 ^ n :=
  ⟨1, by simpa using normalizer_relIndex_dvd_two⟩

end Sporadic.LeechRelated.HS

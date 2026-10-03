module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# Commutators with an index-two subgroup

If `B` has index two in `S`, then `[S,S] = [B,S]`. Two elements outside
`B` differ by an element of `B`; replacing the first by this difference
leaves their commutator unchanged. No finiteness assumption is needed.
-/

namespace Subgroup
open scoped commutatorElement

public theorem commutator_eq_of_relIndex_two
    {G : Type*} [Group G] (B S : Subgroup G)
    (hBS : B ≤ S) (hindex : B.relIndex S = 2) : ⁅S, S⁆ = ⁅B, S⁆ := by
  apply le_antisymm ?_ (commutator_mono hBS le_rfl)
  apply commutator_le.mpr
  intro s hs t ht
  by_cases hsB : s ∈ B
  · exact commutator_mem_commutator hsB ht
  by_cases htB : t ∈ B
  · rw [commutator_comm B S]
    exact commutator_mem_commutator hs htB
  have hdiff : s * t⁻¹ ∈ B := by
    apply (B.subgroupOf S).mul_mem_iff_of_index_two hindex
      (a := (⟨s, hs⟩ : S)) (b := (⟨t, ht⟩ : S)⁻¹) |>.mpr
    change s ∈ B ↔ t⁻¹ ∈ B
    simp only [inv_mem_iff, hsB, htB]
  have heq : ⁅s, t⁆ = ⁅s * t⁻¹, t⁆ := by
    simp only [commutatorElement_def]
    group
  rw [heq]
  exact commutator_mem_commutator hdiff ht

end Subgroup

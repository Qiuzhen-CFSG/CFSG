module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.Transitions
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Representatives

/-!
# Reduction of the first Fi23 stabilizer bound to residual tree edges

The checked tree removes all non-loop second-generator transitions and both
orientations of the first-generator tree edges. The involution relation leaves
only one orientation of the remaining first-generator edges. The theorem
below applies these reductions to the actual carrier and actual auxiliary
subgroup. Fixed-point loops and residual links are explicit remaining
certificate obligations; no unconditional stabilizer containment is asserted.

Source: ATLAS F23G1-p31671B0, and the first prefix step for the involution
centralizer in GLS3 Table 5.3u and the Fischer paragraph near line 1042 in
`refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection
open FirstTree
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

private theorem aTree_reverse (x : Fin 31671) : aTree (generatorA x) = aTree x := by
  simp only [aTree, ← generatorA_apply_eq_sourceA, generatorA_involutive]
  exact Bool.or_comm _ _

/-- The fixed-point loops and one orientation of every non-tree involution
edge suffice for all first-generator transitions. -/
theorem first_a_edges_of_residual
    (hloops : ∀ x : Fin 31671, generatorA x = x → edge generatorA x ∈ KernelUpperData.first)
    (hlinks : ∀ x : Fin 31671, x.val < (generatorA x).val → aTree x = false →
      edge generatorA x ∈ KernelUpperData.first)
    (x : Fin 31671) : edge generatorA x ∈ KernelUpperData.first := by
  by_cases hfix : generatorA x = x
  · exact hloops x hfix
  by_cases ht : aTree x = true
  · rw [a_tree_edge_eq_one x ht]
    exact KernelUpperData.first.one_mem
  have hf : aTree x = false := Bool.eq_false_iff.mpr ht
  have hn : x.val ≠ (generatorA x).val := fun h => hfix (Fin.ext h.symm)
  rcases lt_or_gt_of_ne hn with h | h
  · exact hlinks x h hf
  · have hr : aTree (generatorA x) = false := (aTree_reverse x).trans hf
    have hm := hlinks (generatorA x) (by simpa only [generatorA_involutive] using h) hr
    rw [a_edge_reverse] at hm
    simpa only [inv_inv] using KernelUpperData.first.inv_mem hm

/-- Exact consumer of the two remaining finite certificate families. This
conditional theorem is not the requested unconditional `first_stabilizer_le`. -/
theorem first_stabilizer_le_of_residual_edges
    (hAloops : ∀ x : Fin 31671, generatorA x = x → edge generatorA x ∈ KernelUpperData.first)
    (hBloops : ∀ x : Fin 31671, generatorB x = x → edge generatorB x ∈ KernelUpperData.first)
    (hlinks : ∀ x : Fin 31671, x.val < (generatorA x).val → aTree x = false →
      edge generatorA x ∈ KernelUpperData.first)
    (g : Carrier) (hg : inclusion g 1 = 1) : inclusion g ∈ KernelUpperData.first := by
  have all_edges : ∀ s ∈ ({generatorA, generatorB} : Set (Equiv.Perm (Fin 31671))),
      ∀ x, edge s x ∈ KernelUpperData.first := by
    intro s hs x
    rcases hs with rfl | hs
    · exact first_a_edges_of_residual hAloops hlinks x
    · have hs' : s = generatorB := Set.mem_singleton_iff.mp hs
      subst s
      by_cases hx : generatorB x = x
      · exact hBloops x hx
      · rw [b_edge_eq_one x hx]
        exact KernelUpperData.first.one_mem
  apply carrier_stabilizer_le_of_transitions KernelUpperData.first representative 1 1
    representative_one
  · intro s hs x
    refine ⟨s x, ⟨edge s x, all_edges s hs x⟩, ?_⟩
    simp only [edge, mul_assoc, mul_inv_cancel_left]
  · intro s hs x
    refine ⟨s⁻¹ x, ⟨(edge s (s⁻¹ x))⁻¹,
      KernelUpperData.first.inv_mem (all_edges s hs (s⁻¹ x))⟩, ?_⟩
    simp [edge, mul_inv_rev, mul_assoc]
  · intro k
    exact KernelUpperData.first_fixes k.property
  · intro x hx
    have he : x = 1 := (representative_base x).symm.trans hx
    simpa only [he] using representative_one
  · exact hg

end Sporadic.Fischer.Fi23.CentralizerSection

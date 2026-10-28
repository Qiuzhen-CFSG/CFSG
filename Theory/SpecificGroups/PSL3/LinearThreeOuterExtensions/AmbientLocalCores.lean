module

public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Diagram
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.CoreCalculation
public import Theory.SpecificGroups.PSL3Even.TauGeometry.Actors
public import Theory.GroupTheory.SylowKernelCore

/-!
# Local-preserving actors and cores in ambient PSL₃ extensions

An automorphism preserving either actual local preserves its characteristic
root-plane two-core, hence its full geometric parabolic normalizer. Preservation
of one diagram type excludes the graph coset. The local join core calculation
therefore applies inside the linear-field subgroup, and its literal inclusion
transports the result back to the full automorphism group. Over the field of
order two the diagram kernel is inner; a normalizing two-element is then
implemented by an element of the selected local.

Source: Aschbacher–Smith F.1.12, printed pp.263–264, and the local calculation
used in E.1.14(1), p.214. No global diagram-triviality hypothesis is imposed.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3 Matrix.PSL3.LinearThree
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open Matrix.PSL3.RootPlaneGeometry Matrix.PSL3Even.UnipotentGeometry
open Theory.GroupTheory.AutomorphismExtensionBorel
namespace Matrix.PSL3.LinearThree.OuterExtensions.AmbientLocalCores
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The characteristic local core is the literal geometric root plane. -/
theorem local_core_eq_rootPlane {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (b : Bool) : (localFactor F b).pCoreIn 2 = rootPlane F b := by
  have hU : unipotent F ≤ localFactor F b := by
    cases b
    · exact unipotent_le_lineLocal F
    · exact unipotent_le_pointLocal F
  have hc : (localFactor F b).pCoreIn 2 ≤ (projective F).range := by
    rw [projective_range]
    have h := pCoreIn_le_sylow (localFactor F b) ((unipotentSylow F hf hF).subtype hU)
    change (localFactor F b).pCoreIn 2 ≤
      ((unipotent F).subgroupOf (localFactor F b)).map (localFactor F b).subtype at h
    rwa [map_subgroupOf_eq_of_le hU] at h
  rw [← Subgroup.map_comap_eq_self hc]
  change (((pCore 2 (localFactor F b)).map (localFactor F b).subtype).comap
    (projective F)).map (projective F) = _
  rw [Matrix.PSL3Even.TauGeometry.core_comap_projective]
  cases b <;> exact (Subgroup.map_map _ _ _).symm

/-- Preserving one local excludes graph actors, including over the binary field. -/
theorem preserving_local_mem_linearField {f : ℕ} (hf : 0 < f)
    (hF : Nat.card F = 2^f) (b : Bool) (a : MulAut PSL(3,F))
    (ha : (localFactor F b).map a.toMonoidHom = localFactor F b) :
    a ∈ linearField F := by
  have hc : (rootPlane F b).map a.toMonoidHom = rootPlane F b := by
    rw [← local_core_eq_rootPlane F hf hF b, map_pCoreIn_of_injective 2 _ _ a.injective, ha]
  have hp : (parabolic F b).map a.toMonoidHom = parabolic F b := by
    rw [← normalizer_rootPlane F b, map_equiv_normalizer_eq, hc]
  apply (mapsParabolicType_self_iff_mem_linearField F hf hF a b).mp
  refine ⟨1, ?_⟩
  rw [map_one]
  exact hp.trans (Subgroup.map_id _).symm

/-- A binary normalizing two-element has an implementer in the actual local. -/
theorem binary_two_element_local (hF : Nat.card F = 2) (b : Bool)
    (a : MulAut PSL(3,F))
    (ha : (localFactor F b).map a.toMonoidHom = localFactor F b)
    (hp : ∃ k : ℕ, a^(2^k) = 1) :
    ∃ x ∈ localFactor F b, a = MulAut.conj x := by
  have hi := preserving_local_mem_linearField F (f := 1) (by decide) (by simpa using hF) b a ha
  rw [linearField_eq_inner_of_card_two F hF] at hi
  obtain ⟨x, rfl⟩ := hi
  obtain ⟨y, rfl⟩ := projection_surjective F x
  have hy : MulAut.conj (projection F y) = linearConj F (SpecialLinearGroup.toGL y) :=
    (linearConj_toGL F y).symm
  rw [hy] at ha hp ⊢
  obtain ⟨k, hk⟩ := hp
  obtain ⟨z, hz⟩ := CoreCalculation.linear_two_element_local F b _
    (CoreCalculation.linear_preserves_shape F b _ ha) k hk
  refine ⟨projection F z.val, ?_, hz⟩
  simpa only [CoreCalculation.localProjectEquiv_val] using
    (CoreCalculation.localProjectEquiv F b z).property

/-- The two cores agree after the literal inclusion into the full automorphism group. -/
theorem local_join_core_in_aut {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (b : Bool) (U : Subgroup (MulAut PSL(3,F)))
    (hU : ∀ a ∈ U, (localFactor F b).map a.toMonoidHom = localFactor F b) :
    ((localFactor F b).map MulAut.conj ⊔ U).pCoreIn 2 =
      ((localFactor F b).map MulAut.conj).pCoreIn 2 := by
  let E := linearField F
  have hinner : MulAut.innerSubgroup PSL(3,F) ≤ E :=
    (inner_le_innerDiagonal F).trans le_sup_left
  have hUE : U ≤ E := fun a ha => preserving_local_mem_linearField F hf hF b a (hU a ha)
  let S := U.subgroupOf E
  have hS : S ≤ normalizer (localIn F E hinner b : Set E) := by
    intro a ha
    rw [localIn, ← rootIn_eq_map]
    exact (mem_normalizer_rootIn_iff _ E hinner (inner_injective F) a).mpr (hU a.val ha)
  have hm : (localIn F E hinner b).map E.subtype = (localFactor F b).map MulAut.conj := by
    rw [localIn, Subgroup.map_map]
    rfl
  have hs : S.map E.subtype = U := map_subgroupOf_eq_of_le hUE
  have hc := local_join_twoCore_eq F E hinner le_rfl b S hS
  change (localIn F E hinner b ⊔ S).pCoreIn 2 = (localIn F E hinner b).pCoreIn 2 at hc
  have hh := congrArg (Subgroup.map E.subtype) hc
  rw [map_pCoreIn_of_injective 2 _ _ E.subtype_injective,
    map_pCoreIn_of_injective 2 _ _ E.subtype_injective, Subgroup.map_sup, hm, hs] at hh
  exact hh

end Matrix.PSL3.LinearThree.OuterExtensions.AmbientLocalCores

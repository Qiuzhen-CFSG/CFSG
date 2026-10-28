module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Sections
public import Theory.GroupAction.SubgroupConjugation

/-!
# Recovering literal exchanged sections from the source quotient images

F.9.18 distinguishes I, its T- and H-orbits, and I_K = [I_H,K].
Full K₀-commutator generation lifts its equality of central images to the
literal equation I_T = I + I^t. The centralizer description of I_K then
implies [I,K^t] = 0, without asserting that T normalizes K.

The hypotheses below are the individual image and centralizer clauses to
be supplied by the full F.9.18(5iii) output. These are transport lemmas,
not a replacement for its complete list of alternatives.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.1.40--42,
pp.31--32; F.9.18(5iii), pp.325--326; and 15.3.65(i), printed p.1152.
-/

@[expose] public section
open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- Orbit spans are monotone in their acting subgroup. -/
theorem orbitSpan_mono_actor {T H : Subgroup D} (hTH : T ≤ H)
    (I : Submodule (ZMod 2) V) : orbitSpan ρ T I ≤ orbitSpan ρ H I := by
  apply iSup_le
  intro t
  exact le_iSup_of_le (⟨t, hTH t.property⟩ : H) le_rfl

/-- The larger H-orbit image suffices to identify the T-orbit literally.
Only K₀, not the individual component K, is normalized by T. -/
theorem orbitSpan_eq_pair_of_ambient_image {K₀ T H : Subgroup D}
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K₀ T I)
    (hTH : T ≤ H) {t : D} (ht : t ∈ T)
    (himage : (orbitSpan ρ H I).map (fixedSpace ρ K₀).mkQ =
      (I ⊔ rightConjugate ρ I t).map (fixedSpace ρ K₀).mkQ) :
    orbitSpan ρ T I = I ⊔ rightConjugate ρ I t := by
  apply orbitSpan_eq_sup_of_quotientImage_eq ρ hI.normalizes hI.isIrrPlus ht
  apply le_antisymm
  · rw [← himage]
    exact Submodule.map_mono (orbitSpan_mono_actor ρ hTH I)
  · exact Submodule.map_mono (sup_le (le_orbitSpan ρ T I)
      (rightConjugate_le_orbitSpan ρ T I ht))

/-- A central-image inclusion places I inside the actual K-commutator
space. Its invariance follows from relative normalization inside K₀. -/
theorem le_component_commutator_of_image {K K₀ H : Subgroup D}
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ K₀ I)
    (hK₀H : K₀ ≤ H) (hK : K₀ ≤ normalizer (K : Set D))
    (himage : I.map (fixedSpace ρ K₀).mkQ ≤
      (subspaceCommutator ρ (orbitSpan ρ H I) K).map (fixedSpace ρ K₀).mkQ) :
    I ≤ subspaceCommutator ρ (orbitSpan ρ H I) K := by
  exact le_of_quotientImage_le ρ hI.choose_spec.1
    (subspaceCommutator_invariant_normalizer ρ
      (hK₀H.trans (orbitSpan_invariant ρ H I)) hK) himage

/-- The source centralizer identity gives literal cross-centralization;
it is not merely centralization after a further quotient. -/
theorem cross_commutator_eq_bot_of_source_images {K K₀ H : Subgroup D}
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ K₀ I)
    (hK₀H : K₀ ≤ H) (hK : K₀ ≤ normalizer (K : Set D)) (t : D)
    (himage : I.map (fixedSpace ρ K₀).mkQ ≤
      (subspaceCommutator ρ (orbitSpan ρ H I) K).map (fixedSpace ρ K₀).mkQ)
    (hcentralizer : subspaceCommutator ρ (orbitSpan ρ H I) K =
      orbitSpan ρ H I ⊓ fixedSpace ρ (K.conjBy t⁻¹)) :
    subspaceCommutator ρ I (K.conjBy t⁻¹) = ⊥ := by
  apply (subspaceCommutator_eq_bot_iff ρ I (K.conjBy t⁻¹)).mpr
  have hi := le_component_commutator_of_image ρ hI hK₀H hK himage
  rw [hcentralizer] at hi
  exact hi.trans inf_le_right

omit ρ in
/-- A genuinely moved component gives the literal outside-normalizer clause. -/
theorem not_mem_normalizer_of_right_conjugate_ne {K : Subgroup D} {t : D}
    (hne : K ≠ K.conjBy t⁻¹) : t ∉ normalizer (K : Set D) := by
  intro ht
  exact hne (mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (K : Set D)).inv_mem ht)).symm

/-- Simultaneous literal conclusions, retaining the same source element t
and all three distinct orbit/commutator spaces in the assumptions. -/
theorem literal_pair_of_source_images {K K₀ T H : Subgroup D}
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K₀ T I)
    (hTH : T ≤ H) (hK₀H : K₀ ≤ H) (hK : K₀ ≤ normalizer (K : Set D))
    {t : D} (ht : t ∈ T) (hne : K ≠ K.conjBy t⁻¹)
    (hpair : (orbitSpan ρ H I).map (fixedSpace ρ K₀).mkQ =
      (I ⊔ rightConjugate ρ I t).map (fixedSpace ρ K₀).mkQ)
    (hfirst : I.map (fixedSpace ρ K₀).mkQ ≤
      (subspaceCommutator ρ (orbitSpan ρ H I) K).map (fixedSpace ρ K₀).mkQ)
    (hcentralizer : subspaceCommutator ρ (orbitSpan ρ H I) K =
      orbitSpan ρ H I ⊓ fixedSpace ρ (K.conjBy t⁻¹)) :
    t ∈ T ∧ t ∉ normalizer (K : Set D) ∧
      orbitSpan ρ T I = I ⊔ rightConjugate ρ I t ∧
      subspaceCommutator ρ I (K.conjBy t⁻¹) = ⊥ := by
  exact ⟨ht, not_mem_normalizer_of_right_conjugate_ne hne,
    orbitSpan_eq_pair_of_ambient_image ρ hI hTH ht hpair,
    cross_commutator_eq_bot_of_source_images ρ hI.isIrrPlus hK₀H hK t hfirst hcentralizer⟩

/-- With right conjugates, the action on I^t pulls back by conjugation
by t, so `RemainingModels.exchangedAction` must receive t⁻¹. -/
theorem rightConjugate_action (t g : D) (v : V) :
    ρ g (ρ t⁻¹ v) = ρ t⁻¹ (ρ (t * g * t⁻¹) v) := by
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged

module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.PairPositioning
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.FourGroupGeometry

/-!
# Initial source positioning for an arbitrary nonsingular elementary group

Nondegeneracy and the pure-2A zero-form theorem select an actual second-class
involution with an outer partner. Its native conjugacy class puts the seed in
the group. The pair-preserving Mathieu placement then gives exact Figure 2
rows unless the selected outer partner has a fixed-point-free Mathieu image.
All conjugations are retained, including their full ambient centralizer and
normalizer transports. The remaining fixed-point-free case is the input to
the still-needed ABB(3) enlargement, not an assumed exclusion.

Source: Kleidman--Wilson (1988), opening of Section 2.3 and Lemma 2.3.1, p.492.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages
open Cardinality.QuotientCount.Image ElementaryEightGeometry InvolutionCentralizers.Second
open LargeCenterRadicals.OuterHalf
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel

/-- An arbitrary nontrivial nonsingular elementary group has an actual native
positioning, with only the fixed-point-free outer-pair branch left explicit. -/
theorem nonsingular_source_positioning (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hX : X ≠ ⊥) (hform : (intrinsicElementaryForm X).Nondegenerate) :
    ∃ g : Model,
      let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
      Y ≤ Local ∧ (seed : Model) ∈ Y ∧
      ((∃ z : Local, (z : Model) ∈ Y ∧ orderOf (starHom z) = 2 ∧
          ∀ x : Fin 24, (starHom z).val x ≠ x) ∨
        (pairPermutation ∈ (Y.subgroupOf Local).map starHom ∧
          ((Y.subgroupOf Local).map starHom ≤ boxImage ∨
            ∃ k : Fin 5, (Y.subgroupOf Local).map starHom = Refinement.exactRow k))) ∧
      centralizer (Y : Set Model) = (centralizer (X : Set Model)).map
        (MulAut.conj g⁻¹).toMonoidHom ∧
      normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
        (MulAut.conj g⁻¹).toMonoidHom := by
  let : Nontrivial X := X.nontrivial_iff_ne_bot.mpr hX
  obtain ⟨t,ht,ht2,_,htclass⟩ := nonzero_form_contains_second X hform.ne_zero
  have ht1 : t ≠ 1 := by intro h; simp [h] at ht2
  have houter : ∃ y : X, ¬ InnerRelated t y := by
    by_contra! h
    have hz : Additive.ofMul (⟨t,ht⟩ : X) = 0 := hform.1 _ (by
      intro y
      exact (intrinsicElementaryForm_eq_zero_iff X _ _ (by
        intro he
        exact ht1 (congrArg (fun z : Additive X => (z.toMul : Model)) he))).mpr (h y.toMul))
    exact ht1 (congrArg (fun z : Additive X => (z.toMul : Model)) hz)
  obtain ⟨y,hy⟩ := houter
  have hsclass : IsConj (seed : Model) ((a*b*a*b*b)^5) :=
    ((OuterReduction.involution_isConj_of_max1_odd_index
      OuterReduction.max1_odd_index_unconditional seed_order).resolve_left
      Cardinality.LocalInvolutionCensus.not_isConj_z_t).symm
  obtain ⟨u,hu⟩ := isConj_iff.mp (hsclass.trans htclass)
  let Z := X.map (MulAut.conj u⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map _
  have hseed : (seed : Model) ∈ Z := by
    exact mem_map.mpr ⟨t,ht,by rw [← hu]; simp [mul_assoc]⟩
  have hZL : Z ≤ Local := Z.le_centralizer.trans
    ((centralizer_le (Set.singleton_subset_iff.mpr hseed)).trans ambient_le_max1)
  let v := MulAut.conj u⁻¹ (y : Model)
  have hv : v ∈ Z := mem_map_of_mem _ y.property
  have hout : ¬ InnerRelated (seed : Model) v := by
    intro h
    apply hy
    have he : MulAut.conj u⁻¹ t = (seed : Model) := by rw [← hu]; simp [mul_assoc]
    exact (innerRelated_equiv (MulAut.conj u⁻¹) t y).mp (he ▸ h)
  rcases source_outer_exact_positioning Z hseed v hv hout with hfree | ⟨w,hwL,hws,hwp,hrow,_,_⟩
  · exact ⟨u,hZL,hseed,Or.inl hfree,
      (map_centralizer_equiv (X : Set Model) (MulAut.conj u⁻¹)).symm,
      (map_equiv_normalizer_eq X (MulAut.conj u⁻¹)).symm⟩
  · let g : Model := u * (w.val : Model)
    have he : Z.map (MulAut.conj (w.val : Model)⁻¹).toMonoidHom =
        X.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [map_map]
      congr 1
      ext x
      simp [g,mul_assoc]
    refine ⟨g,he ▸ hwL,he ▸ hws,Or.inr ⟨he ▸ hwp,he ▸ hrow⟩,?_,?_⟩
    · exact (map_centralizer_equiv (X : Set Model) (MulAut.conj g⁻¹)).symm
    · exact (map_equiv_normalizer_eq X (MulAut.conj g⁻¹)).symm

end Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages

module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxResidualGeometry
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxApplication

/-!
# Whole-normalizer placement for the four large residual box rows

An elementary group with quotient image of order greater than eight cannot
remain in any of the eight exact residual box rows. The checked source
reduction therefore supplies a zero-form witness through the ABB, fixed-tetrad,
or native-eight branch. For each of the four order-eight residual images,
BoxResidualGeometry supplies either such a witness directly or a canonical
central enlargement with larger image. The whole original normalizer is
retained throughout, and maximality gives its exact E/F or pure-first endpoint.

This closes literal residual rows 4–7. Rows 1–3 and the remaining pure-first
normalizers belong to the independent final cover assembly.
Source: Kleidman--Wilson (1988), Section 2.3, pp.492–493.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.BoxResidual
open Cardinality.QuotientCount.Image
open ElementaryEightGeometry hiding Local
open InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open BoxImages
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel

private theorem image_conj (X : Subgroup Model) (hXM : X ≤ Local) (g : Local) :
    ((X.map (MulAut.conj (g : Model)).toMonoidHom).subgroupOf Local).map starHom =
      ((X.subgroupOf Local).map starHom).map (MulAut.conj (starHom g)).toMonoidHom := by
  apply le_antisymm
  · rintro p ⟨y,hy,rfl⟩
    obtain ⟨x,hx,he⟩ := hy
    let x0 : Local := ⟨x,hXM hx⟩
    have hye : y = g*x0*g⁻¹ := by
      apply Subtype.ext
      exact he.symm
    refine ⟨starHom x0,mem_map_of_mem starHom (show x0 ∈ X.subgroupOf Local from hx),?_⟩
    rw [hye,map_mul,map_mul,map_inv]
    rfl
  · rintro p ⟨v,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨g*x*g⁻¹,?_,?_⟩
    · exact mem_map.mpr ⟨x,hx,rfl⟩
    · simp only [map_mul,map_inv,MulEquiv.coe_toMonoidHom,MulAut.conj_apply]

private theorem transport_zero (X : Subgroup Model) (g : Model)
    (Z : Subgroup Model) [IsElementaryAbelian 2 Z] (hZ : Z ≠ ⊥)
    (hzero : intrinsicElementaryForm Z = 0)
    (hN : normalizer (X.map (MulAut.conj g⁻¹).toMonoidHom : Set Model) ≤
      normalizer (Z : Set Model)) :
    ∃ W : Subgroup Model, W ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 W,
      intrinsicElementaryForm W = 0 ∧ normalizer (X : Set Model) ≤ normalizer (W : Set Model) := by
  let W := Z.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hW : W ≠ ⊥ := fun h => hZ
    ((map_eq_bot_iff_of_injective Z (MulAut.conj g).injective).mp h)
  refine ⟨W,hW,inferInstance,intrinsicForm_zero_map Z W (MulAut.conj g) rfl hzero,?_⟩
  have ht := map_mono (f := (MulAut.conj g).toMonoidHom) hN
  rw [map_equiv_normalizer_eq] at ht
  have he : (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X := by
    rw [map_map]
    have hf : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id Model := by ext x; simp [mul_assoc]
    rw [hf,map_id]
  rwa [he,map_equiv_normalizer_eq] at ht

/-- An image larger than every residual box is closed by the existing exact
source reduction, fixed-tetrad/ABB enlargement, and native-eight geometry. -/
theorem large_image_zero_enlargement (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hp : pairPermutation ∈ (X.subgroupOf Local).map starHom)
    (hlarge : 8 < Nat.card ((X.subgroupOf Local).map starHom)) :
    ∃ W : Subgroup Model, W ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 W,
      intrinsicElementaryForm W = 0 ∧ normalizer (X : Set Model) ≤ normalizer (W : Set Model) := by
  rcases NonsingularImages.source_normalizer_reduction X hs hp with
    ⟨g,hYL,hys,hyp,hbox⟩ | hzero | ⟨g,_,hN⟩
  · let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
    let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
    rcases source_box_reduction Y hys hyp hbox with ⟨r,hr⟩ | ⟨Z,hZ,hZe,hzero,hNZ⟩
    · have hXM : X ≤ Local := X.le_centralizer.trans
        ((centralizer_le (Set.singleton_subset_iff.mpr hs)).trans ambient_le_max1)
      have hcard : Nat.card ((Y.subgroupOf Local).map starHom) =
          Nat.card ((X.subgroupOf Local).map starHom) := by
        have hi := image_conj X hXM g.val⁻¹
        change (Y.subgroupOf Local).map starHom = _ at hi
        rw [hi]
        exact card_map_of_injective (MulAut.conj (starHom g.val⁻¹)).injective
      have hb := residual_card_le r
      rw [← hr,hcard] at hb
      omega
    · let : IsElementaryAbelian 2 Z := hZe
      exact transport_zero X (g.val : Model) Z hZ hzero hNZ
  · exact hzero
  · exact NonsingularImages.native_eight_zero_enlargement X g hN

/-- All four literal order-eight residual box images have a nontrivial
zero-form witness invariant under their entire ambient normalizer. -/
theorem large_row_zero_enlargement (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (r : Fin 4)
    (hrow : (X.subgroupOf Local).map starHom = residualImage (largeRow r)) :
    ∃ W : Subgroup Model, W ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 W,
      intrinsicElementaryForm W = 0 ∧ normalizer (X : Set Model) ≤ normalizer (W : Set Model) := by
  rcases source_radical_or_large_omega X hs r hrow with hrad | hlarge
  · exact ⟨NonsingularC.zeroWitness X,hrad,inferInstance,
      NonsingularC.zeroWitness_form X,NonsingularC.zeroWitness_normalizer X⟩
  · let Z := omegaCenterIn (centralizer (X : Set Model))
    have hXZ : X ≤ Z := elementary_le_centralizer_omegaCenter X
    have hp : pairPermutation ∈ (X.subgroupOf Local).map starHom := by
      rw [hrow]
      exact subset_closure ⟨0,rfl⟩
    have hpZ : pairPermutation ∈ (Z.subgroupOf Local).map starHom :=
      map_mono (show X.subgroupOf Local ≤ Z.subgroupOf Local from fun x hx => hXZ hx) hp
    obtain ⟨W,hW,hWe,hzero,hNW⟩ := large_image_zero_enlargement Z (hXZ hs) hpZ hlarge
    let : IsElementaryAbelian 2 W := hWe
    exact ⟨W,hW,inferInstance,hzero,(normalizer_le_centralizer_omegaCenter_normalizer X).trans hNW⟩

/-- Literal maximal-two-local consumer. No extra centralizer or signed-lift
premise remains for these four rows. -/
theorem maximal_large_row_normalizer (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (r : Fin 4)
    (hrow : (X.subgroupOf Local).map starHom = residualImage (largeRow r))
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    (∃ g : Model, normalizer (X : Set Model) =
      LinearFive.M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) = max1.map (MulAut.conj g).toMonoidHom) ∨
    ∃ Z : Subgroup Model, Z ≠ ⊥ ∧ IsElementaryAbelian 2 Z ∧
      normalizer (X : Set Model) = normalizer (Z : Set Model) ∧
      ∀ z ∈ Z, z ≠ 1 → IsConj a z := by
  obtain ⟨Z,hZ,hZe,hzero,hN⟩ := large_row_zero_enlargement X hs r hrow
  let : IsElementaryAbelian 2 Z := hZe
  have he : normalizer (X : Set Model) = normalizer (Z : Set Model) :=
    hmax.eq_of_le ⟨Z,hZ,IsElementaryAbelian.isPGroup 2 Z,rfl⟩ hN
  by_cases hpure : ∀ z ∈ Z, z ≠ 1 → IsConj a z
  · exact Or.inr ⟨Z,hZ,hZe,he,hpure⟩
  · exact M22Images.ZeroFormMaximal.maximal_mixed_zero_form Z _ hzero hpure hmax he

end Janko4.LocalStructure.ElementaryNormalizerCover.BoxResidual

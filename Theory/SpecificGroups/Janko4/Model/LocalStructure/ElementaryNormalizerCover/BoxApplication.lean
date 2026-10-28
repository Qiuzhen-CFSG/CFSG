module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxImages
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ABB.Application
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.NativeEightApplication

/-!
# Whole-normalizer reduction to eight literal box images

The ABB enlargement handles fixed-point-free quotient elements. The exhaustive
binary refinement and fixed-tetrad radical calculation then replace the open
box-containment alternative by equality with one of eight explicit residual
images. The native elementary-eight branch is discharged by its already proved
invariant zero-form subgroup. Transport retains the original ambient conjugator
and whole normalizer; maximality gives equality with the enlarged normalizer.

The final consumer applies the completed mixed zero-form analysis, leaving
native E/F coverage, a pure-first normalizer, or one of the eight residual box
images. The latter two branches and the full four-local cover remain open.
Source: Kleidman--Wilson (1988), Section 2.3, pp.492--493.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.BoxImages
open Cardinality.QuotientCount.Image
open ElementaryEightGeometry hiding Local
open InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel

theorem source_box_reduction (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hp : pairPermutation ∈ (X.subgroupOf Local).map starHom)
    (hbox : (X.subgroupOf Local).map starHom ≤ NonsingularImages.boxImage) :
    (∃ r : Fin 8, (X.subgroupOf Local).map starHom = residualImage r) ∨
    ∃ Z : Subgroup Model, Z ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 Z,
      intrinsicElementaryForm Z = 0 ∧ normalizer (X : Set Model) ≤ normalizer (Z : Set Model) := by
  by_cases hf : ∀ p ∈ (X.subgroupOf Local).map starHom, ∃ i : Fin 24, p.val i = i
  · rcases subgroup_residual_or_tetrad _ hbox hp hf with hr | ⟨r,hr⟩
    · exact Or.inl hr
    · obtain ⟨hne,hzero,hle⟩ := BoxTetrads.source_zeroWitness X hs r hr
      exact Or.inr ⟨NonsingularC.zeroWitness X,hne,inferInstance,hzero,hle⟩
  · push Not at hf
    obtain ⟨p,hp,hfree⟩ := hf
    obtain ⟨z,hz,rfl⟩ := hp
    exact Or.inr (ABB.free_image_zero_enlargement X hs z hz hfree)

private theorem transport_zero_enlargement (X : Subgroup Model) (g : Model)
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

theorem nonsingular_normalizer_reduction (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hX : X ≠ ⊥) (hform : (intrinsicElementaryForm X).Nondegenerate) :
    (∃ (g : Model) (r : Fin 8),
      let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
      Y ≤ Local ∧ (seed : Model) ∈ Y ∧
        pairPermutation ∈ (Y.subgroupOf Local).map starHom ∧
        (Y.subgroupOf Local).map starHom = residualImage r) ∨
    ∃ Z : Subgroup Model, Z ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 Z,
      intrinsicElementaryForm Z = 0 ∧ normalizer (X : Set Model) ≤ normalizer (Z : Set Model) := by
  rcases ABB.nonsingular_normalizer_reduction X hX hform with
    ⟨g,hYL,hys,hp,hbox⟩ | hzero | ⟨g,_,hN⟩
  · let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
    let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
    rcases source_box_reduction Y hys hp hbox with ⟨r,hr⟩ | ⟨Z,hZ,hZe,hzero,hNZ⟩
    · exact Or.inl ⟨g,r,hYL,hys,hp,hr⟩
    · let : IsElementaryAbelian 2 Z := hZe
      exact Or.inr (transport_zero_enlargement X g Z hZ hzero hNZ)
  · exact Or.inr hzero
  · exact Or.inr (NonsingularImages.native_eight_zero_enlargement X g hN)

theorem maximal_nonsingular_normalizer_reduction (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hX : X ≠ ⊥) (hform : (intrinsicElementaryForm X).Nondegenerate)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    (∃ (g : Model) (r : Fin 8),
      let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
      Y ≤ Local ∧ (seed : Model) ∈ Y ∧
        pairPermutation ∈ (Y.subgroupOf Local).map starHom ∧
        (Y.subgroupOf Local).map starHom = residualImage r) ∨
    ∃ Z : Subgroup Model, Z ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 Z,
      intrinsicElementaryForm Z = 0 ∧ normalizer (X : Set Model) = normalizer (Z : Set Model) := by
  rcases nonsingular_normalizer_reduction X hX hform with h | ⟨Z,hZ,hZe,hzero,hN⟩
  · exact Or.inl h
  · let : IsElementaryAbelian 2 Z := hZe
    exact Or.inr ⟨Z,hZ,hZe,hzero,hmax.eq_of_le
      ⟨Z,hZ,IsElementaryAbelian.isPGroup 2 Z,rfl⟩ hN⟩

theorem maximal_nonsingular_local_reduction (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hX : X ≠ ⊥) (hform : (intrinsicElementaryForm X).Nondegenerate)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    (∃ (g : Model) (r : Fin 8),
      let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
      Y ≤ Local ∧ (seed : Model) ∈ Y ∧
        pairPermutation ∈ (Y.subgroupOf Local).map starHom ∧
        (Y.subgroupOf Local).map starHom = residualImage r) ∨
    (∃ g : Model, normalizer (X : Set Model) =
      LinearFive.M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) = max1.map (MulAut.conj g).toMonoidHom) ∨
    ∃ Z : Subgroup Model, Z ≠ ⊥ ∧ IsElementaryAbelian 2 Z ∧
      normalizer (X : Set Model) = normalizer (Z : Set Model) ∧
      ∀ z ∈ Z, z ≠ 1 → IsConj a z := by
  rcases maximal_nonsingular_normalizer_reduction X hX hform hmax with
    h | ⟨Z,hZ,hZe,hzero,hN⟩
  · exact Or.inl h
  · let : IsElementaryAbelian 2 Z := hZe
    by_cases hpure : ∀ z ∈ Z, z ≠ 1 → IsConj a z
    · exact Or.inr (Or.inr ⟨Z,hZ,hZe,hN,hpure⟩)
    · exact Or.inr (M22Images.ZeroFormMaximal.maximal_mixed_zero_form Z
        (normalizer (X : Set Model)) hzero hpure hmax hN)

end Janko4.LocalStructure.ElementaryNormalizerCover.BoxImages

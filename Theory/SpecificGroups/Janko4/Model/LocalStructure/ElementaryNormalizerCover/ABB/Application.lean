module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ABB.Positioning

/-!
# Maximal-two-local application of the ABB(3) enlargement

At a maximal TWO-local, the fixed-point-free ABB(3) branch either remains in
the literal box alternative, enlarges to a zero-form normalizer, or reaches
the fixed native elementary-eight normalizer. The equalities use maximality
among actual two-locals and retain the same ambient conjugators as the source
reduction.

Source: Kleidman--Wilson (1988), Section 2.3 and Corollary 2.3.7,
printed pp.492--493.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ABB
open ElementaryEightGeometry hiding Local
open InvolutionCentralizers.Second
open LargeCenterRadicals.OuterHalf
open LinearFive
open scoped IsMulCommutative

private theorem undo_conj (X : Subgroup Model) (g : Model) :
    (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X := by
  rw [map_map]
  ext x
  simp [mul_assoc]

/-- Maximal TWO-local reduction after the fixed-point-free ABB(3) enlargement.
The box branch remains explicit; the other branches are exact maximal
normalizers of the enlarged zero-form group or of the native elementary-eight
centralizer. -/
theorem maximal_nonsingular_normalizer_reduction
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hX : X ≠ ⊥) (hform : (intrinsicElementaryForm X).Nondegenerate)
    (hM : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    (∃ g : Model,
      let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
      Y ≤ InvolutionCentralizers.Second.Local ∧ (InvolutionCentralizers.Second.seed : Model) ∈ Y ∧
        pairPermutation ∈
          (Y.subgroupOf InvolutionCentralizers.Second.Local).map
            InvolutionCentralizers.Second.starHom ∧
        (Y.subgroupOf InvolutionCentralizers.Second.Local).map
            InvolutionCentralizers.Second.starHom ≤ NonsingularImages.boxImage) ∨
    (∃ Z : Subgroup Model, Z ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 Z,
      intrinsicElementaryForm Z = 0 ∧ normalizer (X : Set Model) = normalizer (Z : Set Model)) ∨
    (∃ g : Model, normalizer (X : Set Model) =
      (normalizer (nativeEight 1 : Set Model)).map (MulAut.conj g).toMonoidHom) := by
  rcases nonsingular_normalizer_reduction X hX hform with hbox | ⟨Z,hZ,hZe,hzero,hNZ⟩ | ⟨g,hC,hNg⟩
  · exact Or.inl hbox
  · let : IsElementaryAbelian 2 Z := hZe
    have hlocal : IsTwoLocal (normalizer (Z : Set Model)) :=
      ⟨Z,hZ,IsElementaryAbelian.isPGroup 2 Z,rfl⟩
    exact Or.inr (Or.inl ⟨Z,hZ,hZe,hzero,
      hM.eq_of_le hlocal hNZ⟩)
  · have hE : nativeEight 1 ≠ ⊥ := by
      intro h
      have hc := nativeEight_card 1
      rw [h,card_bot] at hc
      contradiction
    have hlocal : IsTwoLocal (normalizer (nativeEight 1 : Set Model)) :=
      ⟨nativeEight 1,hE,IsElementaryAbelian.isPGroup 2 _,rfl⟩
    have hle := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hNg
    have hid : ((normalizer (X : Set Model)).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom = normalizer (X : Set Model) := by
      simpa only [inv_inv] using undo_conj (normalizer (X : Set Model)) g⁻¹
    rw [hid] at hle
    exact Or.inr (Or.inr ⟨g⁻¹,hM.eq_of_le (hlocal.map_equiv (MulAut.conj g⁻¹)) hle⟩)

end Janko4.LocalStructure.ElementaryNormalizerCover.ABB

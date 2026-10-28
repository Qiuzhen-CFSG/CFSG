module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.Applications
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.NormalizerAssembly

/-!
# Closing the native elementary-eight branch

The exact nonsingular-row reduction leaves one common order-256 centralizer.
The independent native elementary-eight calculation supplies a nontrivial
order-16 isotropic subgroup whose intrinsic form is zero and whose full
normalizer contains the eight normalizer.  Conjugating this subgroup by the
same ambient element preserves the original normalizer.  Maximality among
actual two-locals therefore replaces the exceptional order-256 branch by the
already checked zero-form alternatives, with the literal ambient conjugator
and normalizer equality retained.

Source: Kleidman--Wilson (1988), Corollary 2.3.6 and Proposition 2.2.3,
printed pp.491--493.  The native invariant subgroup is supplied by
`ElementaryEightGeometry.NormalizerAssembly`; no quotient-table or subgroup
coatom premise is used here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages
open Cardinality.QuotientCount.Image
open ElementaryEightGeometry hiding Local
open InvolutionCentralizers.Second
open LargeCenterRadicals.OuterHalf
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel

/-- The common native order-256 branch reduces to the checked E/F or pure-2A
branches once its invariant zero-form subgroup is adjoined. -/
theorem source_maximal_eight_reduction
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hM : IsMaximalTwoLocal (normalizer (X : Set Model)))
    (hE : ∃ g : Model, normalizer (X : Set Model) =
      (normalizer (nativeEight 1 : Set Model)).map (MulAut.conj g).toMonoidHom) :
    (∃ g : Model, normalizer (X : Set Model) =
        LinearFive.M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) =
        max1.map (MulAut.conj g).toMonoidHom) ∨
    ∃ Z : Subgroup Model, Z ≠ ⊥ ∧ IsElementaryAbelian 2 Z ∧
      normalizer (X : Set Model) = normalizer (Z : Set Model) ∧
      ∀ z ∈ Z, z ≠ 1 → IsConj a z := by
  obtain ⟨g,hg⟩ := hE
  obtain ⟨Y,hY,hYne,hYe,_,hzero,hNY⟩ :=
    ElementaryEightGeometry.nativeEight_invariant_zero_form 1
  let W := Y.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hWne : W ≠ ⊥ := by
    intro h
    apply hYne
    exact (map_eq_bot_iff_of_injective Y (MulAut.conj g).injective).mp h
  have hN : normalizer (X : Set Model) ≤ normalizer (W : Set Model) := by
    rw [hg]
    exact (map_mono (f := (MulAut.conj g).toMonoidHom) hNY).trans_eq
      (map_equiv_normalizer_eq Y (MulAut.conj g))
  have hXW : normalizer (X : Set Model) = normalizer (W : Set Model) := by
    exact hM.eq_of_le
      ⟨W,hWne,IsElementaryAbelian.isPGroup 2 W,rfl⟩ hN
  by_cases hpure : ∀ z ∈ W, z ≠ 1 → IsConj a z
  · exact Or.inr ⟨W,hWne,inferInstance,hXW,hpure⟩
  · rcases M22Images.ZeroFormMaximal.maximal_mixed_zero_form W
      (normalizer (X : Set Model))
      (intrinsicForm_zero_map Y W (MulAut.conj g) rfl hzero) hpure hM hXW with h |
      ⟨Z,hZ,hZe,hHZ,hpureZ⟩
    · exact Or.inl h
    · exact Or.inr ⟨Z,hZ,inferInstance,hHZ,hpureZ⟩

/-- Exhaustive exact-row reduction at maximal-two-local level, with the
native elementary-eight branch discharged by the invariant zero-form
subgroup.  The marked box branch remains explicit for its independent
geometric consumer. -/
theorem source_maximal_reduction_closed
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hp : pairPermutation ∈ (X.subgroupOf Local).map starHom)
    (hM : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    (∃ g : localCentralizer,
      let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
      Y ≤ Local ∧ (seed : Model) ∈ Y ∧
        pairPermutation ∈ (Y.subgroupOf Local).map starHom ∧
        (Y.subgroupOf Local).map starHom ≤ boxImage) ∨
    (∃ g : Model, normalizer (X : Set Model) =
        LinearFive.M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) =
        max1.map (MulAut.conj g).toMonoidHom) ∨
    ∃ Z : Subgroup Model, Z ≠ ⊥ ∧ IsElementaryAbelian 2 Z ∧
      normalizer (X : Set Model) = normalizer (Z : Set Model) ∧
      ∀ z ∈ Z, z ≠ 1 → IsConj a z := by
  rcases source_maximal_reduction X hs hp hM with hbox | h | hpure | height
  · exact Or.inl hbox
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hpure)
  · exact Or.inr (source_maximal_eight_reduction X hM height)

/-- Transport the native invariant zero-form subgroup back along the original
row conjugator. This uses the whole normalizer inclusion supplied by the
selected centralizer calculation, without a maximality hypothesis. -/
theorem native_eight_zero_enlargement (X : Subgroup Model) (g : Model)
    (hN : (normalizer (X : Set Model)).map (MulAut.conj g).toMonoidHom ≤
      normalizer (nativeEight 1 : Set Model)) :
    ∃ Z : Subgroup Model, Z ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 Z,
      intrinsicElementaryForm Z = 0 ∧
      normalizer (X : Set Model) ≤ normalizer (Z : Set Model) := by
  obtain ⟨Y,_,hY,hYe,_,hzero,hNY⟩ := nativeEight_invariant_zero_form 1
  let Z := Y.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map _
  have hZ : Z ≠ ⊥ := fun he => hY
    ((map_eq_bot_iff_of_injective Y (MulAut.conj g⁻¹).injective).mp he)
  refine ⟨Z,hZ,inferInstance,intrinsicForm_zero_map Y Z (MulAut.conj g⁻¹) rfl hzero,?_⟩
  have ht := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (hN.trans hNY)
  rw [map_map,map_equiv_normalizer_eq] at ht
  have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id Model := by
    ext x
    simp [mul_assoc]
  rwa [hid,map_id] at ht

/-- The original arbitrary radical application after exact source-row
selection. Every non-box case now has a nontrivial zero-form witness in the
same radical; the full restricted normalizer and both core maps are retained. -/
theorem source_radical_zero_restriction (P X : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 X] (hs : (seed : Model) ∈ X)
    (hp : pairPermutation ∈ (X.subgroupOf Local).map starHom)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    (∃ g : localCentralizer,
      let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
      Y ≤ Local ∧ (seed : Model) ∈ Y ∧ pairPermutation ∈ (Y.subgroupOf Local).map starHom ∧
        (Y.subgroupOf Local).map starHom ≤ boxImage) ∨
    (∃ Z : Subgroup Model, ∃ _ : IsElementaryAbelian 2 Z,
      let H := normalizer (Z : Set Model)
      Z ≠ ⊥ ∧ Z ≤ P ∧ intrinsicElementaryForm Z = 0 ∧
      IsTwoLocal H ∧ normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P) := by
  have hred : (∃ g : localCentralizer,
      let Y := X.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom
      Y ≤ Local ∧ (seed : Model) ∈ Y ∧ pairPermutation ∈ (Y.subgroupOf Local).map starHom ∧
        (Y.subgroupOf Local).map starHom ≤ boxImage) ∨
      ∃ Z : Subgroup Model, Z ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 Z,
        intrinsicElementaryForm Z = 0 ∧
        normalizer (X : Set Model) ≤ normalizer (Z : Set Model) := by
    rcases source_normalizer_reduction X hs hp with hbox | hzero | ⟨g,_,hNg⟩
    · exact Or.inl hbox
    · exact Or.inr hzero
    · exact Or.inr (native_eight_zero_enlargement X g hNg)
  rcases hred with hbox | ⟨Z,hZ,hZe,hzero,hNZ⟩
  · exact Or.inl hbox
  let : IsElementaryAbelian 2 Z := hZe
  let H := normalizer (Z : Set Model)
  have hNH : normalizer (P : Set Model) ≤ H := hNX.trans hNZ
  have hPH : P ≤ H := P.le_normalizer.trans hNH
  have hZP : Z ≤ P := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
    P Z hP.isPGroup (IsElementaryAbelian.isPGroup 2 Z) hP.2.le hNH
  have hnn := hNH.trans H.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf H hPH hnn
  refine Or.inr ⟨Z,hZe,hZ,hZP,hzero,
    ⟨Z,hZ,IsElementaryAbelian.isPGroup 2 Z,rfl⟩,hNH,hPH,?_,
    hP.subgroupOf_of_normalizer_normalizes H hPH hnn,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPH,map_subgroupOf_eq_of_le hNH]
  · rw [hcore,map_subgroupOf_eq_of_le hPH]

end Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages

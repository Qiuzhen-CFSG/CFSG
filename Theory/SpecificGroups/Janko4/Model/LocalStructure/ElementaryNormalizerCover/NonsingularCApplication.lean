module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularC
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.ZeroFormMaximal

/-!
# Whole-normalizer applications of the (c)/(c′) enlargement

The proved nontrivial zero-form witness preserves a maximal TWO-local
normalizer. The exhaustive mixed zero-form reduction then leaves native E/F
coverage or a pure-2A normalizer in this selected nonsingular source branch.

The arbitrary-radical consumer retains the literal ambient conjugation,
original star quotient, local normalizer image and both two-core maps. Radical
saturation places the new zero-form witness in the same P. These statements
close the weak enlargement for the selected rows; source-wide row selection,
the pure-2A family and the other nonsingular configurations remain necessary
for the full four-local cover.

Source: Kleidman--Wilson (1988), Proposition 2.3.3 and Corollary 2.3.7,
printed pp.492--493, followed by maximal-two-local selection.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularC
open Cardinality QuotientCount.Image KernelCount
open LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis

/-- At maximal TWO-local level the selected (c)/(c′) branch reduces to E/F
coverage or a pure-2A normalizer. No nonsingular alternative remains in this row. -/
theorem maximal_source_c (X H : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hrow : (X.subgroupOf M).map starHom = wholeImage ∨
      (X.subgroupOf M).map starHom = primedImage) (g : Model)
    (hH : IsMaximalTwoLocal H)
    (hHX : H = normalizer (X.map (MulAut.conj g).toMonoidHom : Set Model)) :
    (∃ k : Model, H = M_F.map (MulAut.conj k).toMonoidHom ∨
      H = max1.map (MulAut.conj k).toMonoidHom) ∨
    (∃ Y : Subgroup Model, Y ≠ ⊥ ∧ IsElementaryAbelian 2 Y ∧
      H = normalizer (Y : Set Model) ∧ ∀ y ∈ Y, y ≠ 1 → IsConj a y) := by
  let Y := (zeroWitness X).map (MulAut.conj g).toMonoidHom
  obtain ⟨hY,hYe,hzero,hn⟩ := source_conjugate_zero_enlargement X hs hrow g
  let : IsElementaryAbelian 2 Y := hYe
  have hHY : H = normalizer (Y : Set Model) :=
    hH.eq_of_le ⟨Y,hY,IsElementaryAbelian.isPGroup 2 Y,rfl⟩ (hHX ▸ hn)
  by_cases hp : ∀ y ∈ Y, y ≠ 1 → IsConj a y
  · exact Or.inr ⟨Y,hY,inferInstance,hHY,hp⟩
  exact M22Images.ZeroFormMaximal.maximal_mixed_zero_form Y H hzero hp hH hHY

/-- The literal radical restriction for the (c)/(c′) source branch, with its
actual conjugator and original kernel quotient map retained. -/
theorem radical_source_c_restriction (P X : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 X] (hs : (seed : Model) ∈ X)
    (hrow : (X.subgroupOf M).map starHom = wholeImage ∨
      (X.subgroupOf M).map starHom = primedImage) (g : Model)
    (hNX : normalizer (P : Set Model) ≤
      normalizer (X.map (MulAut.conj g).toMonoidHom : Set Model)) :
    let Y := (zeroWitness X).map (MulAut.conj g).toMonoidHom
    ∃ _ : IsElementaryAbelian 2 Y,
    let H := normalizer (Y : Set Model)
    Y ≠ ⊥ ∧ intrinsicElementaryForm Y = 0 ∧ Y ≤ P ∧ IsTwoLocal H ∧
      normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P := by
  dsimp only
  let Y := (zeroWitness X).map (MulAut.conj g).toMonoidHom
  let H := normalizer (Y : Set Model)
  obtain ⟨hY,hYe,hzero,hn⟩ := source_conjugate_zero_enlargement X hs hrow g
  let : IsElementaryAbelian 2 Y := hYe
  have hNH : normalizer (P : Set Model) ≤ H := hNX.trans hn
  have hPH := P.le_normalizer.trans hNH
  have hYP : Y ≤ P := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
    P Y hP.isPGroup (IsElementaryAbelian.isPGroup 2 Y) hP.2.le hNH
  have hN := hNH.trans H.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf H hPH hN
  refine ⟨hYe,hY,hzero,hYP,⟨Y,hY,IsElementaryAbelian.isPGroup 2 Y,rfl⟩,hNH,hPH,?_,
    hP.subgroupOf_of_normalizer_normalizes H hPH hN,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPH,map_subgroupOf_eq_of_le hNH]
  · rw [hcore,map_subgroupOf_eq_of_le hPH]

end Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularC

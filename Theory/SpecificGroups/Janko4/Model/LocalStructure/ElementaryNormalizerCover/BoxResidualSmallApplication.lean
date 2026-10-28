module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxResidualSmall
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxResidualApplication
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxPurePair
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.ZeroFormMaximal
public import Theory.GroupTheory.PRadical.NormalizerRestriction

/-!
# Whole-normalizer applications for the three small residual rows

`BoxResidualSmall` proves the source centralizer calculation for residual
images 1, 2 and 3: the odd orbit of four pair labels supplies a second core
element, and its product with the seed is a nonzero element of the intrinsic
form radical.  This leaf performs the two applications used by the source:
the radical is preserved by the whole ambient normalizer, and maximality
among TWO-locals upgrades the resulting containment to equality.  The
normalizer/core transport for an arbitrary radical keeps the actual local
subgroup and denominator maps.

Source: Kleidman--Wilson (1988), Proposition 2.3.2 and the residual rows of
Figure 2(a), printed pp.492--493.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.BoxResidual
open Cardinality.QuotientCount.Image
open ElementaryEightGeometry hiding Local
open InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open M22Images
open BoxImages
open LinearFive
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel

private theorem transport_small_zero
    (X : Subgroup Model) (g : Model) (Z : Subgroup Model)
    [IsElementaryAbelian 2 Z] (hZ : Z ≠ ⊥)
    (hzero : intrinsicElementaryForm Z = 0)
    (hN : normalizer (X.map (MulAut.conj g⁻¹).toMonoidHom : Set Model) ≤
      normalizer (Z : Set Model)) :
    ∃ W : Subgroup Model, W ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 W,
      intrinsicElementaryForm W = 0 ∧ normalizer (X : Set Model) ≤
        normalizer (W : Set Model) := by
  let W := Z.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hW : W ≠ ⊥ := fun h => hZ
    ((map_eq_bot_iff_of_injective Z (MulAut.conj g).injective).mp h)
  refine ⟨W,hW,inferInstance,
    intrinsicForm_zero_map Z W (MulAut.conj g) rfl hzero,?_⟩
  have ht := map_mono (f := (MulAut.conj g).toMonoidHom) hN
  rw [map_equiv_normalizer_eq] at ht
  have he : (X.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = X := by
    rw [map_map]
    have hf : (MulAut.conj g).toMonoidHom.comp
        (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id Model := by
      ext x
      simp [mul_assoc]
    rw [hf,map_id]
  rwa [he,map_equiv_normalizer_eq] at ht

/-- Every one of the three small residual rows has a nontrivial zero-form
witness normalized by the complete ambient normalizer. -/
theorem small_row_zero_enlargement (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hs : (seed : Model) ∈ X) (r : Fin 3)
    (hrow : (X.subgroupOf M).map starHom = residualImage (smallRow r)) :
    ∃ Z : Subgroup Model, Z ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 Z,
      intrinsicElementaryForm Z = 0 ∧ normalizer (X : Set Model) ≤
        normalizer (Z : Set Model) := by
  obtain ⟨hZ,hzero,hN⟩ := small_row_zeroWitness X hs r hrow
  exact ⟨coreZeroWitness X,hZ,inferInstance,hzero,hN⟩

/-- Maximal TWO-local equality for a small residual row, followed by the
source pure/mixed zero-form split. -/
theorem maximal_small_row_normalizer (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hs : (seed : Model) ∈ X) (r : Fin 3)
    (hrow : (X.subgroupOf M).map starHom = residualImage (smallRow r))
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    (∃ g : Model, normalizer (X : Set Model) =
      LinearFive.M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) = max1.map (MulAut.conj g).toMonoidHom) ∨
    ∃ Z : Subgroup Model, Z ≠ ⊥ ∧ IsElementaryAbelian 2 Z ∧
      normalizer (X : Set Model) = normalizer (Z : Set Model) ∧
      ∀ z ∈ Z, z ≠ 1 → IsConj a z := by
  obtain ⟨Z,hZ,hZe,hzero,hN⟩ := small_row_zero_enlargement X hs r hrow
  let : IsElementaryAbelian 2 Z := hZe
  have he : normalizer (X : Set Model) = normalizer (Z : Set Model) :=
    hmax.eq_of_le ⟨Z,hZ,IsElementaryAbelian.isPGroup 2 Z,rfl⟩ hN
  by_cases hpure : ∀ z ∈ Z, z ≠ 1 → IsConj a z
  · exact Or.inr ⟨Z,hZ,inferInstance,he,hpure⟩
  · exact M22Images.ZeroFormMaximal.maximal_mixed_zero_form Z
      (normalizer (X : Set Model)) hzero hpure hmax he

/-- The arbitrary-radical consumer for a small residual row. -/
theorem radical_small_row_restriction
    (P X : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 X] (hs : (seed : Model) ∈ X) (r : Fin 3)
    (hrow : (X.subgroupOf M).map starHom = residualImage (smallRow r))
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ Z : Subgroup Model, ∃ _ : IsElementaryAbelian 2 Z,
      let H := normalizer (Z : Set Model)
      Z ≠ ⊥ ∧ Z ≤ P ∧ intrinsicElementaryForm Z = 0 ∧
      IsTwoLocal H ∧ normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype =
        normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P := by
  obtain ⟨Z,hZ,hZe,hzero,hNZ⟩ := small_row_zero_enlargement X hs r hrow
  let : IsElementaryAbelian 2 Z := hZe
  let H := normalizer (Z : Set Model)
  have hNH : normalizer (P : Set Model) ≤ H := hNX.trans hNZ
  have hPH : P ≤ H := P.le_normalizer.trans hNH
  have hZP : Z ≤ P := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
    P Z hP.isPGroup (IsElementaryAbelian.isPGroup 2 Z) hP.2.le hNH
  have hnn := hNH.trans H.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf H hPH hnn
  refine ⟨Z,inferInstance,hZ,hZP,hzero,
    ⟨Z,hZ,IsElementaryAbelian.isPGroup 2 Z,rfl⟩,hNH,hPH,?_,
    hP.subgroupOf_of_normalizer_normalizes H hPH hnn,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPH,map_subgroupOf_eq_of_le hNH]
  · rw [hcore,map_subgroupOf_eq_of_le hPH]

/-- Assembly of all eight exact residual rows.  Row zero is the cyclic
pure-second branch, rows one through three are the odd-orbit calculations in
this leaf, and rows four through seven use the canonical large-row
enlargement. -/
theorem maximal_residual_row_reduction
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (r : Fin 8)
    (hrow : (X.subgroupOf M).map starHom = residualImage r)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    (∃ g : Model, normalizer (X : Set Model) =
      LinearFive.M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) = max1.map (MulAut.conj g).toMonoidHom) ∨
    ∃ Z : Subgroup Model, Z ≠ ⊥ ∧ IsElementaryAbelian 2 Z ∧
      normalizer (X : Set Model) = normalizer (Z : Set Model) ∧
      ∀ z ∈ Z, z ≠ 1 → IsConj a z := by
  fin_cases r
  · obtain ⟨Z,hZ,hZe,hzero,hN⟩ :=
      BoxPurePair.source_pair_maximal_zeroWitness X hs hrow hmax
    by_cases hpure : ∀ z ∈ Z, z ≠ 1 → IsConj a z
    · exact Or.inr ⟨Z,hZ,hZe,hN,hpure⟩
    · exact M22Images.ZeroFormMaximal.maximal_mixed_zero_form Z
        (normalizer (X : Set Model)) hzero hpure hmax hN
  · exact maximal_small_row_normalizer X hs 0 hrow hmax
  · exact maximal_small_row_normalizer X hs 1 hrow hmax
  · exact maximal_small_row_normalizer X hs 2 hrow hmax
  · exact maximal_large_row_normalizer X hs 0 hrow hmax
  · exact maximal_large_row_normalizer X hs 1 hrow hmax
  · exact maximal_large_row_normalizer X hs 2 hrow hmax
  · exact maximal_large_row_normalizer X hs 3 hrow hmax

end Janko4.LocalStructure.ElementaryNormalizerCover.BoxResidual

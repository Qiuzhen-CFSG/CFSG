module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Reducibility.MatrixConditions
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.OuterImageComparison.MatrixComparison
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.Alignment


/-!
# Identifying the max2 quotient with the concrete binary action group

The published quotient matrices use row actions. Conjugation by the first
certified basis change, inverse transpose, and the second basis change send
these generators to the certified raw generators in `actionGroup`. The forward
and reverse word certificates give equality of the generated groups.

The alignment follows the private construction in `Max2Exclusion.MathieuMap`;
this version also proves surjectivity. Matrix provenance: the unchanged ATLAS
files in `TwoCoreNormalizer/LinearModel/source/`, attributed there to Wilson,
Nickerson and Bray. Source application: Aschbacher–Smith, Proposition 1.3.4,
printed p.511/PDF p.528, and GLS3 Table 5.3i.
-/

public section
open Subgroup
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreCentralizerData.LowerBound TwoCoreCentralizerData.OuterImageComparison
open TwoCoreComparison.CoordinateGenerators TwoCoreLinearModel

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2

private def inverseTransposeUnit (u : Matrix12ˣ) : Matrix12ˣ where
  val := (↑u⁻¹ : Matrix12).transpose
  inv := (↑u : Matrix12).transpose
  val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

private def inverseTranspose : Matrix12ˣ ≃* Matrix12ˣ where
  toFun := inverseTransposeUnit
  invFun := inverseTransposeUnit
  left_inv u := Units.ext rfl
  right_inv u := Units.ext rfl
  map_mul' u v := by
    apply Units.ext
    change (↑(u * v)⁻¹ : Matrix12).transpose =
      (↑u⁻¹ : Matrix12).transpose * (↑v⁻¹ : Matrix12).transpose
    rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem inverseTranspose_x : inverseTranspose actionUnitX = rawUnitX := by
  apply Units.ext
  decide +kernel

private theorem inverseTranspose_y : inverseTranspose actionUnitY = rawUnitY := by
  apply Units.ext
  decide +kernel

/-- The two basis changes with the necessary change from row to column actions. -/
def cubicMatrixAlignment : QuotientMatrixˣ ≃* Matrix12ˣ :=
  ((MulAut.conj changeBasisUnit).trans inverseTranspose).trans (MulAut.conj basisUnit)

/-- The first published quotient generator in the aligned column convention. -/
theorem cubicMatrixAlignment_quotientX :
    cubicMatrixAlignment quotientX = MulAut.conj basisUnit rawUnitX := by
  change MulAut.conj basisUnit (inverseTranspose
    (changeBasisUnit * quotientX * changeBasisUnit⁻¹)) = _
  rw [← conjugate_x]
  simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel_right,
    inverseTranspose_x]

/-- The second published quotient generator in the aligned column convention. -/
theorem cubicMatrixAlignment_quotientY :
    cubicMatrixAlignment quotientY = MulAut.conj basisUnit rawUnitY := by
  change MulAut.conj basisUnit (inverseTranspose
    (changeBasisUnit * quotientY * changeBasisUnit⁻¹)) = _
  rw [← conjugate_y]
  simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel_right,
    inverseTranspose_y]

attribute [local irreducible] cubicMatrixAlignment inverseTranspose inverseTransposeUnit

/-- Both certified generating sets give the same matrix group after alignment. -/
theorem cubicMatrixAlignment_map :
    quotientSubgroup.map cubicMatrixAlignment.toMonoidHom = actionGroup := by
  rw [quotientSubgroup, MonoidHom.map_closure, Set.image_pair]
  simp only [MulEquiv.coe_toMonoidHom, cubicMatrixAlignment_quotientX, cubicMatrixAlignment_quotientY]
  apply le_antisymm
  · exact (closure_le _).mpr (by
      rintro x (rfl | rfl)
      · exact conjugated_rawX_mem
      · exact conjugated_rawY_mem)
  · apply (closure_le _).mpr
    let H := Subgroup.closure {MulAut.conj basisUnit rawUnitX, MulAut.conj basisUnit rawUnitY}
    have hx : MulAut.conj basisUnit rawUnitX ∈ H := subset_closure (Or.inl rfl)
    have hy : MulAut.conj basisUnit rawUnitY ∈ H := subset_closure (Or.inr rfl)
    rintro x (rfl | rfl)
    · change unitC ∈ H
      rw [← align_first]
      simp only [firstWord, map_pow, map_mul]
      exact H.pow_mem (H.mul_mem hx hy) 7
    · change unitD ∈ H
      rw [← align_second]
      simp only [secondWord, map_mul, map_inv, map_pow]
      exact
        H.mul_mem (H.mul_mem (H.inv_mem (H.mul_mem (H.mul_mem hx hy) hx))
          (H.pow_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
            (H.pow_mem (H.mul_mem hx hy) 3) hy) (H.pow_mem (H.mul_mem hx hy) 2)) hy)
            (H.pow_mem (H.mul_mem hx hy) 2)) 3)) (H.mul_mem (H.mul_mem hx hy) hx)

/-- An actual equivalence of the quotient matrix carrier and the ATLAS action group. -/
def matrixEquivActionGroup : MatrixGroup ≃* actionGroup :=
  (cubicMatrixAlignment.subgroupMap quotientSubgroup).trans
    (MulEquiv.subgroupCongr cubicMatrixAlignment_map)


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate.Max2

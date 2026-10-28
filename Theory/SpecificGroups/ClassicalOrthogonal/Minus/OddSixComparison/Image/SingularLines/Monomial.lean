module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.FieldModel
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.SignedCoordinates
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Image.Root

/-!
# Special unitary monomial lifts for the signed minus-six coordinates

The antidiagonal matrix has determinant one. For the skew scalar t = 2α+1,
the product of diag(t,1,1,-t⁻¹) with the middle-coordinate swap is also
special unitary. We compute all six exterior coordinates of both elements,
then extract the pivot identities used by singular-vector elimination.
In particular, reversal sends the opposite vector to minus the first vector;
the uncorrected middle swap would have determinant minus one.

Source: the twisted A₃/D₃ exterior construction in GLS3 §2.7, used for the
small orthogonal reduction in Aschbacher–Smith A.2.17, printed pp.38–39.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison
open Matrix BenderSuzuki.MatrixGroups Atlas.Order20160A8.Bivectors
open Theory.SpecificGroups.ClassicalUnitary
namespace Image.SingularLines
variable {p n : ℕ} [Fact p.Prime] [NeZero n]
variable {F : Type} [Field F] [Finite F]
variable (R : ExteriorRealization F (Extension p n) (unitaryForm p n))
variable (C : SignedCoordinates R)

omit [NeZero n] in
private theorem reversal_det : (UnitaryFourFlag.gram (Extension p n)).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [UnitaryFourFlag.gram, Fin.sum_univ_succ, Matrix.det_fin_three]
  change (1 : Extension p n) * 1 * 1 - 1 * 0 * 0 = 1
  ring

private theorem reversal_unitary :
    (unitaryForm p n).conjTranspose (UnitaryFourFlag.gram (Extension p n)) *
      (unitaryForm p n).form * UnitaryFourFlag.gram (Extension p n) =
        (unitaryForm p n).form := by
  change (unitaryForm p n).conjTranspose (UnitaryFourFlag.gram (Extension p n)) *
    UnitaryFourFlag.gram (Extension p n) * UnitaryFourFlag.gram (Extension p n) =
      UnitaryFourFlag.gram (Extension p n)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-unitaryForm_conj, HermitianForm.conjTranspose, UnitaryFourFlag.gram,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The antidiagonal special unitary matrix, with determinant one in every characteristic. -/
def reversal : (unitaryForm p n).specialSubgroup :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (UnitaryFourFlag.gram (Extension p n))
    (by rw [reversal_det]; exact one_ne_zero),
    (by exact reversal_unitary), (by exact Units.ext reversal_det)⟩

/-- All six compound coordinates of the reversal. -/
theorem reversal_exterior (w : Six (Extension p n)) :
    exteriorMap (reversal (p := p) (n := n)).val.val w =
      ![-w 5, -w 4, -w 2, -w 3, -w 1, -w 0] := by
  ext i
  fin_cases i <;>
    simp [reversal, UnitaryFourFlag.gram, exteriorMap, compound, first, second,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The middle swap corrected by the skew diagonal matrix. -/
def interchangeMatrix : Matrix (Fin 4) (Fin 4) (Extension p n) :=
  !![2 * C.root + 1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, -(2 * C.root + 1)⁻¹]

theorem interchangeMatrix_det : (interchangeMatrix R C).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [interchangeMatrix, Fin.sum_univ_succ, Matrix.det_fin_three, C.skew_ne_zero]

theorem interchangeMatrix_unitary :
    (unitaryForm p n).conjTranspose (interchangeMatrix R C) *
      (unitaryForm p n).form * interchangeMatrix R C = (unitaryForm p n).form := by
  have htinv : (unitaryForm p n).conj ((2 * C.root + 1)⁻¹) =
      -((2 * C.root + 1)⁻¹) := by
    rw [map_inv₀, conjugation_skew R C, inv_neg]
  change (unitaryForm p n).conjTranspose (interchangeMatrix R C) *
    UnitaryFourFlag.gram (Extension p n) * interchangeMatrix R C =
      UnitaryFourFlag.gram (Extension p n)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-unitaryForm_conj, HermitianForm.conjTranspose, interchangeMatrix,
      UnitaryFourFlag.gram, Matrix.mul_apply, Fin.sum_univ_succ,
      conjugation_skew R C, htinv, C.skew_ne_zero]
  linear_combination mul_inv_cancel₀ C.skew_ne_zero

/-- The corrected swap as an actual special unitary element. -/
def interchange : (unitaryForm p n).specialSubgroup :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (interchangeMatrix R C)
    (by rw [interchangeMatrix_det]; exact one_ne_zero),
    interchangeMatrix_unitary R C, Units.ext (interchangeMatrix_det R C)⟩

/-- All six compound coordinates of the corrected swap, retaining the signs. -/
theorem interchange_exterior (w : Six (Extension p n)) :
    exteriorMap (interchange R C).val.val w =
      ![(2 * C.root + 1) * w 1, (2 * C.root + 1) * w 0,
        -w 2, -w 3, -((2 * C.root + 1)⁻¹ * w 5),
        -((2 * C.root + 1)⁻¹ * w 4)] := by
  ext i
  fin_cases i <;>
    simp [interchange, interchangeMatrix, exteriorMap, compound, first, second,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, C.skew_ne_zero]

include C

theorem reversal_pivot (x : Space F 2) :
    (((R.action reversal).val x).1 0).2 = -(x.1 0).1 := by
  apply R.coefficient.injective
  have he := congrFun (R.intertwines reversal x) 5
  rw [reversal_exterior, C.coordinates_eq, C.coordinates_eq] at he
  simpa [signedBivectors] using he

theorem reversal_second_ne_zero (x : Space F 2) (hc : (x.1 1).1 ≠ 0) :
    (((R.action reversal).val x).1 1).2 ≠ 0 := by
  intro heq
  have he := congrFun (R.intertwines reversal x) 4
  rw [reversal_exterior, C.coordinates_eq, C.coordinates_eq] at he
  have hc' : R.coefficient (x.1 1).1 ≠ 0 := (map_ne_zero _).mpr hc
  simp [signedBivectors, heq, C.skew_ne_zero, hc'] at he

theorem interchange_pivot_ne_zero (x : Space F 2) (hd : (x.1 1).2 ≠ 0) :
    (((R.action (interchange R C)).val x).1 0).2 ≠ 0 := by
  intro heq
  have he := congrFun (R.intertwines (interchange R C) x) 5
  rw [interchange_exterior, C.coordinates_eq, C.coordinates_eq] at he
  have hd' : R.coefficient (x.1 1).2 ≠ 0 := (map_ne_zero _).mpr hd
  simp [signedBivectors, heq, C.skew_ne_zero, hd'] at he

theorem reversal_opposite :
    (R.action reversal).val (opposite F) = -direction F := by
  apply R.coordinates_injective
  rw [R.intertwines, reversal_exterior, C.coordinates_eq, C.coordinates_eq]
  ext i
  fin_cases i <;> simp [-unitaryForm_conj, signedBivectors, opposite, direction]

end Image.SingularLines
end ClassicalOrthogonal.Minus.OddSixComparison

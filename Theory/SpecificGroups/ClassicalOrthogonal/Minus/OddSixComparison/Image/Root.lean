module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.FieldModel
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.SignedCoordinates
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Image.Siegel

/-!
# Signed unitary lifts along the first singular line

For t = 2α+1 and z = ι(x)-αι(y), the upper unipotent with off-diagonal
block [[-z,t c],[d/t,σ(z)]] is special unitary. Its six compound minors
are exactly the Siegel transformation in the prescribed signed coordinates.
This supplies the first-direction input of the independent image argument.
Source: the exterior-square twisted A₃/D₃ construction in GLS3 §2.7,
used by Aschbacher–Smith A.2.17, printed pp.38–39.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison
open Matrix BenderSuzuki.MatrixGroups Atlas.Order20160A8.Bivectors
open Theory.SpecificGroups.ClassicalUnitary
namespace Image
variable {p n : ℕ} [Fact p.Prime] [NeZero n]
variable {F : Type} [Field F] [Finite F]
variable (R : ExteriorRealization F (Extension p n) (unitaryForm p n))
variable (C : SignedCoordinates R)

/-- The anisotropic coordinate in the published signed chart. -/
def normCoordinate (v : Space F 2) : Extension p n :=
  R.coefficient v.2.1 - C.root * R.coefficient v.2.2

theorem conjugation_skew :
    (unitaryForm p n).conj (2 * C.root + 1) = -(2 * C.root + 1) := by
  rw [map_add, map_mul, map_ofNat, map_one, C.root_conjugate]
  ring

/-- The concrete upper unipotent with the odd-characteristic signs. -/
def rootMatrix (v : Space F 2) : Matrix (Fin 4) (Fin 4) (Extension p n) :=
  !![1, 0, -normCoordinate R C v, (2 * C.root + 1) * R.coefficient (v.1 1).1;
     0, 1, (2 * C.root + 1)⁻¹ * R.coefficient (v.1 1).2,
       (unitaryForm p n).conj (normCoordinate R C v);
     0, 0, 1, 0;
     0, 0, 0, 1]

theorem rootMatrix_det (v : Space F 2) : (rootMatrix R C v).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [rootMatrix, Fin.prod_univ_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [rootMatrix]

theorem rootMatrix_unitary (v : Space F 2) :
    (unitaryForm p n).conjTranspose (rootMatrix R C v) *
      (unitaryForm p n).form * rootMatrix R C v = (unitaryForm p n).form := by
  have hs (x : Extension p n) :
      (unitaryForm p n).conj ((unitaryForm p n).conj x) = x :=
    (unitaryForm p n).conj_involutive x
  have htinv : (unitaryForm p n).conj ((2 * C.root + 1)⁻¹) =
      -((2 * C.root + 1)⁻¹) := by
    rw [map_inv₀, conjugation_skew, inv_neg]
  change (unitaryForm p n).conjTranspose (rootMatrix R C v) *
    UnitaryFourFlag.gram (Extension p n) * rootMatrix R C v =
      UnitaryFourFlag.gram (Extension p n)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-unitaryForm_conj, HermitianForm.conjTranspose, rootMatrix, UnitaryFourFlag.gram,
      Matrix.mul_apply, Fin.sum_univ_succ, C.coefficient_fixed,
      conjugation_skew, hs, htinv]
  all_goals ring

/-- An actual SU₄ element; no abstract root-group identification is used. -/
def rootLift (v : Space F 2) : (unitaryForm p n).specialSubgroup :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (rootMatrix R C v)
    (by rw [rootMatrix_det]; exact one_ne_zero),
    rootMatrix_unitary R C v, Units.ext (rootMatrix_det R C v)⟩

@[simp] theorem rootLift_val (v : Space F 2) :
    (rootLift R C v).val.val = rootMatrix R C v := rfl

private theorem polar_coordinates (v w : Space F 2) :
    (quadraticForm F 3).polarBilin v w =
      (v.1 0).1 * (w.1 0).2 + (v.1 0).2 * (w.1 0).1 +
      (v.1 1).1 * (w.1 1).2 + (v.1 1).2 * (w.1 1).1 +
      (2 * v.2.1 * w.2.1 + v.2.1 * w.2.2 + v.2.2 * w.2.1 -
        2 * parameter F * v.2.2 * w.2.2) := by
  change (form F 2 (parameter F)).polarBilin _ _ = _
  rw [form_polar, plane_polar]
  simp [Fin.sum_univ_succ, add_assoc]

/-- The actual six minors agree with the signed Siegel formula. -/
theorem rootLift_exterior (v x : Space F 2)
    (hv : (quadraticForm F 3).polarBilin (direction F) v = 0) :
    exteriorMap (rootLift R C v).val.val (R.coordinates x) =
      R.coordinates (Quadratic.siegel (quadraticForm F 3) (direction F) v x) := by
  have hb : (v.1 0).2 = 0 := (polar_direction F v).symm.trans hv
  have hp : (quadraticForm F 3).polarBilin x (direction F) = (x.1 0).2 :=
    (Quadratic.polar_swap _ _ _).trans (polar_direction F x)
  have ha : R.coefficient (parameter F) = C.root ^ 2 + C.root := C.root_equation.symm
  rw [rootLift_val, C.coordinates_eq, C.coordinates_eq]
  simp only [Quadratic.siegel, hp]
  rw [polar_coordinates]
  ext i
  fin_cases i <;>
    simp [-unitaryForm_conj, -QuadraticMap.polarBilin_apply_apply,
      rootMatrix, normCoordinate, exteriorMap, compound, first, second,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.vecHead, Matrix.vecTail, smul_eq_mul, map_ofNat,
      signedBivectors, direction, quadraticForm, form_apply,
      hb, C.coefficient_fixed, C.root_conjugate, ha, map_add, map_sub] <;>
    (try field_simp [C.skew_ne_zero]) <;> ring

/-- The first-direction Siegel map is precisely the lifted unitary exterior action. -/
theorem rootLift_action (v : Space F 2)
    (hv : (quadraticForm F 3).polarBilin (direction F) v = 0) :
    R.action (rootLift R C v) =
      siegelElement (quadraticForm F 3) (direction F) v (direction_singular F) hv := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply R.coordinates_injective
  rw [R.intertwines, rootLift_exterior R C v x hv]
  rfl

include C in
/-- All first-direction lifts required by singular-line transport are supplied. -/
theorem direction_siegel_mem_range (v : Space F 2)
    (hv : (quadraticForm F 3).polarBilin (direction F) v = 0) :
    siegelElement (quadraticForm F 3) (direction F) v (direction_singular F) hv ∈
      R.action.range :=
  ⟨rootLift R C v, rootLift_action R C v hv⟩

end Image
end ClassicalOrthogonal.Minus.OddSixComparison

module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag.NativeBridge
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag.NativeAction
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks

/-!
# The certified native eleven-coset flag

The inverse witness gives an actual linear equivalence. Its conjugacy identities
transport the native coset action to the displayed upper triangular matrices.
The quotient construction then supplies all 33 stages and their literal quotient
coordinates. The native action and matrix certificates discharge both finite
obligations, giving `PointSimpleDegrees.flagCoordinates` without hypotheses.
The degree-filtration application retains only the independent factor-simplicity
premise.

Source: James, J. Algebra 27 (1973), 57–111; `PointSimpleDegrees/source/README.md`.
-/

@[expose] public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag

theorem basis_mul_inverse (M : MatrixIdentities) : basisMatrix * inverseMatrix = 1 :=
  (mul_eq_one_comm (a := inverseMatrix) (b := basisMatrix)).mp M.inverse

def matrixEquiv {n : ℕ} (P Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
  { Q.mulVecLin with
    invFun := P.mulVec
    left_inv := fun v => by
      change P.mulVec (Q.mulVec v) = v
      rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
    right_inv := fun v => by
      change Q.mulVec (P.mulVec v) = v
      rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec] }

theorem matrixEquiv_apply {n : ℕ} (P Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (v : Fin n → ZMod 2) :
    matrixEquiv P Q hPQ hQP v = Q.mulVec v := rfl

def basisCoordinates (M : MatrixIdentities) : Space ≃ₗ[ZMod 2] Space :=
  matrixEquiv basisMatrix inverseMatrix (basis_mul_inverse M) M.inverse

theorem basisCoordinates_apply (M : MatrixIdentities) (v : Space) :
    basisCoordinates M v = inverseMatrix.mulVec v :=
  matrixEquiv_apply basisMatrix inverseMatrix (basis_mul_inverse M) M.inverse v

theorem inverse_mul_action (M : MatrixIdentities) (s : Fin 2) :
    inverseMatrix * cosetMatrix s = actionMatrix s * inverseMatrix := by
  calc
    inverseMatrix * cosetMatrix s =
        inverseMatrix * cosetMatrix s * (basisMatrix * inverseMatrix) := by
      rw [basis_mul_inverse M, mul_one]
    _ = inverseMatrix * (cosetMatrix s * basisMatrix) * inverseMatrix := by
      simp only [mul_assoc]
    _ = inverseMatrix * (basisMatrix * actionMatrix s) * inverseMatrix := by
      rw [M.action]
    _ = actionMatrix s * inverseMatrix := by
      rw [← mul_assoc inverseMatrix basisMatrix, M.inverse, one_mul]

def adaptedCoordinates (C : CosetCoordinates) (M : MatrixIdentities) :
    (ElevenCoset → ZMod 2) ≃ₗ[ZMod 2] Space :=
  C.coordinates.trans (basisCoordinates M)

theorem adaptedCoordinates_apply (C : CosetCoordinates) (M : MatrixIdentities)
    (v : ElevenCoset → ZMod 2) :
    adaptedCoordinates C M v = inverseMatrix.mulVec (C.coordinates v) := by
  rw [adaptedCoordinates, LinearEquiv.trans_apply, basisCoordinates_apply]

theorem adaptedCoordinates_generator (C : CosetCoordinates) (M : MatrixIdentities)
    (s : Fin 2) (v : ElevenCoset → ZMod 2) :
    adaptedCoordinates C M (cosetRepresentation (generator s) v) =
      (actionMatrix s).mulVec (adaptedCoordinates C M v) := by
  rw [adaptedCoordinates_apply, adaptedCoordinates_apply, C.generator_coordinates,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    inverse_mul_action M]

theorem upper (M : MatrixIdentities) (m : ℕ) (s : Fin 2) (x y : Fin 720)
    (hx : cut m ≤ x.val) (hy : y.val < cut m) : actionMatrix s x y = 0 := by
  by_cases hm : m < 33
  · exact M.upper ⟨m, hm⟩ s x y hx hy
  · rw [cut_eq_full m (by omega)] at hx
    omega

/-- The actual quotient-flag consumer of the two independent finite certificates. -/
noncomputable def flagCoordinates_of_certificates
    (C : CosetCoordinates) (M : MatrixIdentities) : FlagCoordinates :=
  Construction.flagCoordinates (adaptedCoordinates C M)
    (adaptedCoordinates_generator C M) (upper M) M.diagonal

/-- It suffices to check the native tables and the packed matrix identities. -/
noncomputable def flagCoordinates_of_native_certificates
    (h : NativeBridge.NativeAction) (M : MatrixIdentities) : FlagCoordinates :=
  flagCoordinates_of_certificates (NativeBridge.cosetCoordinates h) M

/-- Application to the degree-filtration interface; factor simplicity is independent. -/
theorem filtration_of_coset_matrix_certificates
    (C : CosetCoordinates) (M : MatrixIdentities) (h : Data.SimpleMatrices) :
    FactorDegreeFiltration ({1, 10, 32, 44} : Set ℕ) cosetRepresentation :=
  filtration_of_certificates (flagCoordinates_of_certificates C M) h

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag

namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees

/-- The 33-stage invariant flag of the actual eleven-coset representation,
with coordinates on its literal successive quotients and native A/B equations. -/
noncomputable def flagCoordinates : FlagCoordinates :=
  CosetFlag.flagCoordinates_of_native_certificates
    CosetFlag.nativeAction CosetFlag.matrixIdentities

/-- The certified native flag discharges the geometric premise of the degree
filtration. Simplicity of the four concrete matrix pairs remains independent. -/
theorem filtration_of_simpleMatrices (h : Data.SimpleMatrices) :
    FactorDegreeFiltration ({1, 10, 32, 44} : Set ℕ) cosetRepresentation :=
  filtration_of_certificates flagCoordinates h

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees

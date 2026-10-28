module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Data
public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.CycleSimplicity.Arithmetic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# A checked adapted basis over every characteristic-two field

One packed binary multiplication proves invertibility of the published
126-dimensional basis. Entrywise scalar extension gives a linear equivalence
over every characteristic-two field. The first column is the constant vector;
the sum of the rows singles out the final coordinate, so the first 125 basis
vectors span precisely augmentation. These are matrix identities, independent
of the outstanding identification of the permutation action with SU₃(5).

Source motivation: Guralnick–Malle, Classification of 2F-modules I,
Proposition 4.3; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors
open Thompson.BinaryMatrix
open scoped BigOperators Matrix

theorem packed_basis_inverse : ∀ i : Fin 126,
    rowProduct basisRows[i.val]! coordinateRows 126 = 2 ^ i.val := by
  decide +kernel

theorem basis_mul_coordinate : basisMatrix * coordinateMatrix = 1 :=
  decode_mul_one 126 basisRows coordinateRows packed_basis_inverse

theorem coordinate_mul_basis : coordinateMatrix * basisMatrix = 1 :=
  (mul_eq_one_comm (a := basisMatrix) (b := coordinateMatrix)).mp basis_mul_coordinate

theorem basis_first_column : ∀ i : Fin 126, basisMatrix i 0 = 1 := by
  decide +kernel

private theorem packed_augmentation :
    rowProduct (2 ^ 126 - 1) basisRows 126 = 2 ^ 125 := by
  decide +kernel

private theorem full_row_bit : ∀ i : Fin 126, bit (2 ^ 126 - 1) i.val = 1 := by
  decide +kernel

theorem basis_column_sum (j : Fin 126) :
    (∑ i, basisMatrix i j) = if j = 125 then 1 else 0 := by
  have h := congrArg (fun r => bit r j.val) packed_augmentation
  rw [bit_rowProduct] at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  simp only [full_row_bit, one_mul] at h
  change (∑ i, basisMatrix i j) = bit (2 ^ 125) j.val at h
  rw [h]
  have hj : (125 : ℕ) = j.val ↔ j = (125 : Fin 126) := by
    rw [Fin.ext_iff]
    exact eq_comm
  simp only [bit, Nat.testBit_two_pow, decide_eq_true_eq, hj]

attribute [local irreducible] basisMatrix coordinateMatrix basisRows coordinateRows

variable (K : Type*) [Field K] [CharP K 2]

theorem cast_basis_mul_coordinate :
    CycleCertificate.castMatrix K basisMatrix * CycleCertificate.castMatrix K coordinateMatrix = 1 := by
  rw [← map_mul, basis_mul_coordinate, map_one]

theorem cast_coordinate_mul_basis :
    CycleCertificate.castMatrix K coordinateMatrix * CycleCertificate.castMatrix K basisMatrix = 1 := by
  rw [← map_mul, coordinate_mul_basis, map_one]

/-- A change of coordinates with explicitly certified inverse matrices. -/
noncomputable def coordinatesOfInverse {n : ℕ}
    (B C : Matrix (Fin n) (Fin n) K) (hBC : B * C = 1) (hCB : C * B = 1) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  { C.mulVecLin with
    invFun := B.mulVec
    left_inv := fun v => by
      change B.mulVec (C.mulVec v) = v
      rw [Matrix.mulVec_mulVec, hBC, Matrix.one_mulVec]
    right_inv := fun v => by
      change C.mulVec (B.mulVec v) = v
      rw [Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec] }

omit [CharP K 2] in
theorem coordinatesOfInverse_symm_apply {n : ℕ}
    (B C : Matrix (Fin n) (Fin n) K) (hBC : B * C = 1) (hCB : C * B = 1)
    (v : Fin n → K) : (coordinatesOfInverse K B C hBC hCB).symm v = B.mulVec v := rfl

/-- The checked adapted coordinates, before identifying the point set with cosets. -/
noncomputable def basisCoordinates : (Fin 126 → K) ≃ₗ[K] (Fin 126 → K) :=
  coordinatesOfInverse K _ _ (cast_basis_mul_coordinate K) (cast_coordinate_mul_basis K)

theorem basisCoordinates_symm_apply (v : Fin 126 → K) :
    (basisCoordinates K).symm v = (CycleCertificate.castMatrix K basisMatrix).mulVec v :=
  coordinatesOfInverse_symm_apply K _ _ _ _ v

theorem cast_basis_first_column (i : Fin 126) :
    CycleCertificate.castMatrix K basisMatrix i 0 = 1 := by
  change (ZMod.castHom (dvd_refl 2) K) (basisMatrix i 0) = 1
  rw [basis_first_column, map_one]

theorem basisCoordinates_constant :
    basisCoordinates K (fun _ => 1) = Pi.single 0 1 := by
  apply (basisCoordinates K).symm.injective
  rw [LinearEquiv.symm_apply_apply, basisCoordinates_symm_apply, Matrix.mulVec_single_one]
  ext i
  exact (cast_basis_first_column K i).symm

theorem cast_basis_column_sum (j : Fin 126) :
    (∑ i, CycleCertificate.castMatrix K basisMatrix i j) = if j = 125 then 1 else 0 := by
  change (∑ i, (ZMod.castHom (dvd_refl 2) K) (basisMatrix i j)) = _
  rw [← map_sum, basis_column_sum]
  split <;> simp

theorem basisCoordinates_symm_sum (v : Fin 126 → K) :
    (∑ i, (basisCoordinates K).symm v i) = v 125 := by
  simp only [basisCoordinates_symm_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, cast_basis_column_sum]
  simp

/-- The final adapted coordinate is exactly augmentation. -/
theorem basisCoordinates_last (v : Fin 126 → K) :
    basisCoordinates K v 125 = ∑ i, v i := by
  simpa using (basisCoordinates_symm_sum K (basisCoordinates K v)).symm

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors

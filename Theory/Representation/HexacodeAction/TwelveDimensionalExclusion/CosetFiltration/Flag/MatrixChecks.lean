module

public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.Flag.Certificates
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.Model

/-!
# Certified basis inverse, generator conjugacy and invariant cuts

Packed columns encode the published basis, whose GAP rows were transposed.
Integer certificates, decoded by the proved arithmetic lemmas, establish the
basis inverse and both generator equations. The zero lower blocks prove that
every specified initial segment is invariant. These identities supply the
adapted linear equivalence for the literal quotient construction in `Flag`.

Source: Aschbacher–Smith K.1.3, printed p.453 / PDF p.464. The fixed witnesses
and ATLAS attribution are recorded in `../source/README.md`; all checks here
run in Lean's kernel.
-/

@[expose] public section
namespace Representation.Hexacode.TwelveDimensional.CosetCertificate.Flag

theorem basis_mul_inverse : basisMatrix * inverseMatrix = 1 := by
  apply Matrix.ext
  intro x y
  have h := congrArg (fun p => entry (code p x.val)) (packed_inverse y)
  rw [decode_combine, decode_power] at h
  simpa only [basisMatrix, inverseMatrix, Matrix.mul_apply, Matrix.one_apply,
    packed_columns_spec, Fin.val_inj, eq_comm] using h

theorem inverse_mul_basis : inverseMatrix * basisMatrix = 1 :=
  (mul_eq_one_comm (a := basisMatrix) (b := inverseMatrix)).mp basis_mul_inverse

theorem basis_mul_adapted (j : Fin 2) :
    basisMatrix * adaptedMatrix j =
      fun x y => coefficient j x * basisMatrix (rowSource j x) y := by
  apply Matrix.ext
  intro x y
  have h := congrArg (fun p => entry (code p x.val)) (packed_action j y)
  rw [decode_combine, decode_pack, decode_mul] at h
  simpa only [basisMatrix, adaptedMatrix, coefficient, Matrix.mul_apply,
    packed_columns_spec] using h

/-- The original monomial matrices and the saved adapted matrices are
conjugate by the published column basis. -/
theorem generator_conjugacy (j : Fin 2) :
    inverseMatrix * generatorMatrix j * basisMatrix = adaptedMatrix j := by
  have h : generatorMatrix j * basisMatrix = basisMatrix * adaptedMatrix j := by
    rw [basis_mul_adapted]
    apply Matrix.ext
    intro x y
    simp [Matrix.mul_apply, generatorMatrix]
  rw [mul_assoc, h, ← mul_assoc, inverse_mul_basis, one_mul]

theorem upper (m : ℕ) (j : Fin 2) (x y : Fin 45)
    (hx : cut m ≤ x.val) (hy : y.val < cut m) : adaptedMatrix j x y = 0 := by
  by_cases hm : m < 10
  · change entry (adaptedRows j x y) = 0
    rw [lower_blocks_zero ⟨m, hm⟩ j x y hx hy]
    rfl
  · have h : cut m = 45 := by simp [cut, hm]
    rw [h] at hx
    omega

def basisCoordinates : Space ≃ₗ[F] Space :=
  { inverseMatrix.mulVecLin with
    invFun := basisMatrix.mulVec
    left_inv := fun v => by
      change basisMatrix.mulVec (inverseMatrix.mulVec v) = v
      rw [Matrix.mulVec_mulVec, basis_mul_inverse, Matrix.one_mulVec]
    right_inv := fun v => by
      change inverseMatrix.mulVec (basisMatrix.mulVec v) = v
      rw [Matrix.mulVec_mulVec, inverse_mul_basis, Matrix.one_mulVec] }

theorem basisCoordinates_symm_apply (v : Space) :
    basisCoordinates.symm v = basisMatrix.mulVec v := rfl

theorem basisCoordinates_generator (j : Fin 2) (v : Space) :
    basisCoordinates (representation (FreeGroup.of j) v) =
      (adaptedMatrix j).mulVec (basisCoordinates v) := by
  have h (w : Space) : basisMatrix.mulVec ((adaptedMatrix j).mulVec w) =
      representation (FreeGroup.of j) (basisMatrix.mulVec w) := by
    rw [Matrix.mulVec_mulVec, basis_mul_adapted]
    funext x
    rw [representation_of_apply]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  apply basisCoordinates.symm.injective
  rw [LinearEquiv.symm_apply_apply, basisCoordinates_symm_apply, h,
    ← basisCoordinates_symm_apply, LinearEquiv.symm_apply_apply]

end Representation.Hexacode.TwelveDimensional.CosetCertificate.Flag

module

public import Theory.SpecificGroups.ClassicalUnitary.FiveFlag

/-!
# Determinant correction preserving the standard unitary-five flag

A unitary matrix has norm-one determinant. Right multiplication by the
matrix `diag(1,1,1,1,det(A)⁻¹)` makes its determinant one and leaves its
action unchanged on the hyperplane with last coordinate zero. In particular,
it preserves the images of both standard isotropic subspaces.

We also verify that two invertible bases with equal Hermitian Gram matrices
differ by a unitary matrix. These are algebraic transport results; existence
of a basis adapted to an arbitrary isotropic subspace is a separate input.

Source: the determinant-correction argument in GLS3, Lemma 2.7.2 and its
proof, printed pp.89–90, in `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity
variable {F : Type*} [Field F] (J : HermitianForm 5 F)

private def lastDiagonal (u : Fˣ) : GL (Fin 5) F where
  val := diagonal (fun i => if i = 4 then u.val else 1)
  inv := diagonal (fun i => if i = 4 then (u⁻¹).val else 1)
  val_inv := by
    rw [diagonal_mul_diagonal, diagonal_eq_one]
    ext i
    split_ifs <;> simp
  inv_val := by
    rw [diagonal_mul_diagonal, diagonal_eq_one]
    ext i
    split_ifs <;> simp

private theorem lastDiagonal_det (u : Fˣ) :
    GeneralLinearGroup.det (lastDiagonal u) = u := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply]
  simp [lastDiagonal, det_diagonal]

private theorem norm_det (A : GL (Fin 5) F)
    (hA : J.conjTranspose A.val * A.val = 1) :
    J.conj A.val.det * A.val.det = 1 := by
  have he : (J.conjTranspose A.val).det = J.conj A.val.det := by
    change (A.val.map J.conj).transpose.det = J.conj A.val.det
    rw [det_transpose, J.conj.map_det]
    rfl
  have hd := congrArg Matrix.det hA
  simpa only [det_mul, he, det_one] using hd

private theorem lastDiagonal_unitary (hJ : J.form = 1) (u : Fˣ)
    (hu : J.conj u.val * u.val = 1) : lastDiagonal u ∈ J.unitarySubgroup := by
  rw [J.mem_unitarySubgroup_iff, hJ, mul_one]
  have he : J.conjTranspose (lastDiagonal u).val =
      diagonal (fun i : Fin 5 => if i = 4 then J.conj u.val else 1) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i = 4 <;> simp [lastDiagonal, HermitianForm.conjTranspose, hi]
    · simp [lastDiagonal, HermitianForm.conjTranspose, hij, Ne.symm]
  rw [he]
  change diagonal _ * diagonal _ = 1
  rw [diagonal_mul_diagonal, diagonal_eq_one]
  ext i
  split_ifs <;> simp [hu]

private theorem lastDiagonal_fixes (u : Fˣ) (v : Fin 5 → F) (hv : v 4 = 0) :
    (lastDiagonal u).val *ᵥ v = v := by
  ext i
  change (diagonal _ *ᵥ v) i = v i
  rw [mulVec_diagonal]
  by_cases hi : i = 4 <;> simp [hi, hv]

/-- Correct a unitary matrix on the last coordinate, fixing its action on
all vectors whose last coordinate vanishes. -/
theorem exists_special_of_unitary (hJ : J.form = 1) (A : GL (Fin 5) F)
    (hA : A ∈ J.unitarySubgroup) :
    ∃ g : J.specialSubgroup, ∀ v : Fin 5 → F, v 4 = 0 →
      linearAction J g v = A.val *ᵥ v := by
  have hA' := (J.mem_unitarySubgroup_iff A).mp hA
  rw [hJ, mul_one] at hA'
  let u := (GeneralLinearGroup.det A)⁻¹
  have hu : J.conj u.val * u.val = 1 := by
    dsimp only [u]
    rw [Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply]
    rw [map_inv₀, ← mul_inv, norm_det J A hA', inv_one]
  have hs : A * lastDiagonal u ∈ J.specialSubgroup := by
    change A * lastDiagonal u ∈ J.unitarySubgroup ∧
      GeneralLinearGroup.det (A * lastDiagonal u) = 1
    exact ⟨J.unitarySubgroup.mul_mem hA (lastDiagonal_unitary J hJ u hu), by
      rw [map_mul, lastDiagonal_det]
      exact mul_inv_cancel _⟩
  refine ⟨⟨A * lastDiagonal u, hs⟩, ?_⟩
  intro v hv
  change (A.val * (lastDiagonal u).val) *ᵥ v = A.val *ᵥ v
  rw [← mulVec_mulVec, lastDiagonal_fixes u v hv]

private theorem adjoint_mul (A B : Matrix (Fin 5) (Fin 5) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem adjoint_one : J.conjTranspose 1 = 1 := by
  change ((J.conj : F →+* F).mapMatrix 1).transpose = _
  rw [map_one, transpose_one]

/-- Two bases with the same Hermitian Gram matrix differ by an actual unitary matrix. -/
theorem unitary_of_same_gram (hJ : J.form = 1) (P C : GL (Fin 5) F)
    (hPC : J.conjTranspose P.val * P.val = J.conjTranspose C.val * C.val) :
    P * C⁻¹ ∈ J.unitarySubgroup := by
  rw [J.mem_unitarySubgroup_iff, hJ, mul_one, Units.val_mul, adjoint_mul]
  calc
    J.conjTranspose (C⁻¹).val * J.conjTranspose P.val * (P.val * (C⁻¹).val) =
        J.conjTranspose (C⁻¹).val * (J.conjTranspose P.val * P.val) * (C⁻¹).val := by
      simp only [mul_assoc]
    _ = J.conjTranspose (C⁻¹).val * (J.conjTranspose C.val * C.val) * (C⁻¹).val := by
      rw [hPC]
    _ = J.conjTranspose (C.val * (C⁻¹).val) * (C.val * (C⁻¹).val) := by
      rw [adjoint_mul]
      simp only [mul_assoc]
    _ = 1 := by simp [adjoint_one]

/-- A unitary image of either standard isotropic subspace is also a special-unitary image. -/
theorem special_image_of_unitary (hJ : J.form = 1) (b : Bool)
    (A : GL (Fin 5) F) (hA : A ∈ J.unitarySubgroup) :
    ∃ g : J.specialSubgroup,
      (if b then plane F else line F).map A.val.mulVecLin =
        (if b then plane F else line F).map (linearAction J g).toLinearMap := by
  obtain ⟨g, hg⟩ := exists_special_of_unitary J hJ A hA
  refine ⟨g, ?_⟩
  have hv (v : Fin 5 → F) (hm : v ∈ (if b then plane F else line F)) :
      linearAction J g v = A.val *ᵥ v := by
    apply hg
    cases b
    · exact hm.2.2.2
    · exact hm.2.2
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, hv w hw⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, (hv w hw).symm⟩

end Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity

module

public import Theory.LinearAlgebra.Hermitian.PrimeFrobeniusNormalization
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Identity Gram matrices and actual unitary group equivalences

For a finite field of order p² with stored conjugation x ↦ x^p, every
nondegenerate Hermitian form admits an orthonormal basis. Conjugation by
its inverse identifies the exact special unitary groups, and conjugation
by its projective class identifies their actual images in PGL.

The algebraic conjugation proofs generalize the dimension-three proofs in
`CFSG/Quasithin/ChapterF/Section01/RankOneBorels/Unitary/FormTransport.lean`
to arbitrary dimension and the identity Gram matrix. Basis existence is
Huppert II.10.4, through `PrimeFrobeniusNormalization`; neither characteristic
two nor a chosen field representation is assumed.
-/

noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.IdentityGram
variable {F : Type*} [Field F] {n : ℕ}

/-- The identity Gram matrix with exactly the original field involution. -/
@[expose] public def identityGram (J : HermitianForm n F) : HermitianForm n F where
  conj := J.conj
  conj_involutive := J.conj_involutive
  form := 1
  form_hermitian := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, Ne.symm]
  form_nondegenerate := by simp

@[simp] public theorem identityGram_conj (J : HermitianForm n F) :
    (identityGram J).conj = J.conj := rfl

@[simp] public theorem identityGram_form (J : HermitianForm n F) :
    (identityGram J).form = 1 := rfl

private theorem adjoint_mul (J : HermitianForm n F)
    (A B : Matrix (Fin n) (Fin n) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem adjoint_one (J : HermitianForm n F) :
    J.conjTranspose 1 = 1 := by
  change ((J.conj : F →+* F).mapMatrix 1).transpose = _
  rw [map_one, transpose_one]

private def adjointUnit (J : HermitianForm n F) (C : GL (Fin n) F) : GL (Fin n) F where
  val := J.conjTranspose C.val
  inv := J.conjTranspose (C⁻¹).val
  val_inv := by rw [← adjoint_mul]; simpa using adjoint_one J
  inv_val := by rw [← adjoint_mul]; simpa using adjoint_one J

private theorem conjugate_preserves_iff (J : HermitianForm n F) (C B : GL (Fin n) F) :
    J.conjTranspose (C * B * C⁻¹).val * J.form * (C * B * C⁻¹).val = J.form ↔
    J.conjTranspose B.val * (J.conjTranspose C.val * J.form * C.val) * B.val =
      J.conjTranspose C.val * J.form * C.val := by
  have he :
      J.conjTranspose B.val * (J.conjTranspose C.val * J.form * C.val) * B.val =
        (adjointUnit J C).val *
          (J.conjTranspose (C * B * C⁻¹).val * J.form * (C * B * C⁻¹).val) * C.val := by
    simp only [Units.val_mul, adjoint_mul]
    change _ = (adjointUnit J C).val *
      (((adjointUnit J C)⁻¹).val * (J.conjTranspose B.val * (adjointUnit J C).val) *
        J.form * (C.val * B.val * (C⁻¹).val)) * C.val
    simp only [← mul_assoc, Units.mul_inv, one_mul, Units.inv_mul_cancel_right]
    rfl
  rw [he]
  change _ ↔ (adjointUnit J C).val * _ * C.val =
    (adjointUnit J C).val * J.form * C.val
  rw [Units.mul_left_inj, Units.mul_right_inj]


/-- Basis change preserves the exact unitary and determinant-one conditions. -/
public theorem special_conjugate_iff (J : HermitianForm n F) (C B : GL (Fin n) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (identityGram J).form) :
    C * B * C⁻¹ ∈ J.specialSubgroup ↔ B ∈ (identityGram J).specialSubgroup := by
  rw [J.mem_specialSubgroup_iff, (identityGram J).mem_specialSubgroup_iff,
    conjugate_preserves_iff, hC]
  simp only [map_mul, map_inv, mul_assoc, mul_mul_inv_cancel'_right]
  rfl

private def restrictConjugation {G : Type*} [Group G] (H K : Subgroup G) (c : G)
    (h : ∀ x, c * x * c⁻¹ ∈ K ↔ x ∈ H) : H ≃* K where
  toFun x := ⟨c * x * c⁻¹, (h x).2 x.property⟩
  invFun x := ⟨c⁻¹ * x * c, (h _).1 (by simp [mul_assoc])⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

/-- The actual matrix conjugation equivalence from an arbitrary SU to identity-form SU. -/
public def specialEquiv (J : HermitianForm n F) (C : GL (Fin n) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (identityGram J).form) :
    J.specialSubgroup ≃* (identityGram J).specialSubgroup :=
  (restrictConjugation _ _ C (fun B => special_conjugate_iff J C B hC)).symm

@[simp] public theorem specialEquiv_apply (J : HermitianForm n F) (C : GL (Fin n) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (identityGram J).form)
    (A : J.specialSubgroup) :
    (specialEquiv J C hC A : GL (Fin n) F) = C⁻¹ * A * C := by rfl

@[simp] public theorem specialEquiv_symm_apply (J : HermitianForm n F) (C : GL (Fin n) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (identityGram J).form)
    (A : (identityGram J).specialSubgroup) :
    ((specialEquiv J C hC).symm A : GL (Fin n) F) = C * A * C⁻¹ := by rfl

/-- Conjugation descends along the genuine quotient map GL → PGL. -/
public theorem projective_conjugate_iff (J : HermitianForm n F) (C : GL (Fin n) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (identityGram J).form)
    (x : Matrix.ProjGenLinGroup (Fin n) F) :
    ProjGenLinGroup.mk C * x * (ProjGenLinGroup.mk C)⁻¹ ∈
        ProjectiveSpecialUnitaryMatrixGroup J ↔
      x ∈ ProjectiveSpecialUnitaryMatrixGroup (identityGram J) := by
  constructor
  · rintro ⟨A, hA, hAx⟩
    refine ⟨C⁻¹ * A * C, ?_, ?_⟩
    · apply (special_conjugate_iff J C _ hC).1
      simpa [mul_assoc] using hA
    · simp only [map_mul, map_inv]
      rw [hAx]
      simp [mul_assoc]
  · rintro ⟨A, hA, rfl⟩
    exact ⟨C * A * C⁻¹, (special_conjugate_iff J C A hC).2 hA,
      by simp only [map_mul, map_inv]⟩

/-- Conjugation on PGL restricts to the actual PSU images. -/
public def projectiveEquiv (J : HermitianForm n F) (C : GL (Fin n) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (identityGram J).form) :
    ProjectiveSpecialUnitaryMatrixGroup J ≃*
      ProjectiveSpecialUnitaryMatrixGroup (identityGram J) :=
  (restrictConjugation _ _ (ProjGenLinGroup.mk C)
    (fun x => projective_conjugate_iff J C hC x)).symm

@[simp] public theorem projectiveEquiv_apply (J : HermitianForm n F) (C : GL (Fin n) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (identityGram J).form)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) :
    (projectiveEquiv J C hC x : ProjGenLinGroup (Fin n) F) =
      (ProjGenLinGroup.mk C)⁻¹ * x * ProjGenLinGroup.mk C := by rfl

@[simp] public theorem projectiveEquiv_symm_apply (J : HermitianForm n F)
    (C : GL (Fin n) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (identityGram J).form)
    (x : ProjectiveSpecialUnitaryMatrixGroup (identityGram J)) :
    ((projectiveEquiv J C hC).symm x : ProjGenLinGroup (Fin n) F) =
      ProjGenLinGroup.mk C * x * (ProjGenLinGroup.mk C)⁻¹ := by rfl

/-- Matrix and projective transport commute with the natural projection. -/
public theorem projectiveEquiv_mk (J : HermitianForm n F) (C : GL (Fin n) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (identityGram J).form)
    (A : J.specialSubgroup) :
    (projectiveEquiv J C hC
      ⟨ProjGenLinGroup.mk (A : GL (Fin n) F), ⟨A, A.property, rfl⟩⟩ :
        ProjGenLinGroup (Fin n) F) =
      ProjGenLinGroup.mk (specialEquiv J C hC A : GL (Fin n) F) := by
  simp only [projectiveEquiv_apply, specialEquiv_apply, map_mul, map_inv]

/-- Orthonormalization gives simultaneous matrix and projective equivalences
in every dimension, retaining the original Frobenius conjugation. -/
public theorem exists_identityGram_transport [Finite F] (J : HermitianForm n F)
    (p : ℕ) (hp : p.Prime) (hcard : Nat.card F = p ^ 2)
    (hconj : ∀ x, J.conj x = x ^ p) :
    ∃ (C : GL (Fin n) F)
      (e : J.specialSubgroup ≃* (identityGram J).specialSubgroup)
      (ep : ProjectiveSpecialUnitaryMatrixGroup J ≃*
        ProjectiveSpecialUnitaryMatrixGroup (identityGram J)),
      J.conjTranspose C.val * J.form * C.val = 1 ∧
      (∀ A : J.specialSubgroup, (e A : GL (Fin n) F) = C⁻¹ * A * C) ∧
      (∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
        (ep x : ProjGenLinGroup (Fin n) F) =
          (ProjGenLinGroup.mk C)⁻¹ * x * ProjGenLinGroup.mk C) := by
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨C, hC⟩ := J.exists_orthonormal_basis_of_prime_frobenius hconj hcard
  exact ⟨C, specialEquiv J C hC, projectiveEquiv J C hC, hC,
    specialEquiv_apply J C hC, projectiveEquiv_apply J C hC⟩

end BenderSuzuki.MatrixGroups.HermitianForm.IdentityGram

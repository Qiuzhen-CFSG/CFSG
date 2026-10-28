module

public import BenderSuzuki.External.Huppert.II.theorem_10_4
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FieldParameters

/-!
# Arbitrary-form transport for SU₃ and PSU₃

For the unitary alternatives of Aschbacher–Smith F.1.3(1), printed pp.259–260,
we replace an arbitrary nondegenerate Hermitian Gram matrix by the antidiagonal
matrix, retaining exactly the stored field involution. Huppert II.10.4 gives
an invertible basis matrix. Conjugation by its inverse identifies the special
unitary groups, and conjugation by its projective class identifies their images
in PGL. All field parameters include n = 1.

The private adjoint cancellation argument adapts the two-dimensional argument
in `BenderSuzuki.MatrixGroups.HermitianConjugation` to dimension three.
-/

noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.Unitary.FormTransport
variable {F : Type*} [Field F]

/-- The antidiagonal form with exactly the original field involution. -/
@[expose] public def standardForm (J : HermitianForm 3 F) : HermitianForm 3 F where
  conj := J.conj
  conj_involutive := J.conj_involutive
  form := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  form_hermitian := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  form_nondegenerate := by simp [Matrix.det_fin_three]

@[simp] public theorem standardForm_conj (J : HermitianForm 3 F) :
    (standardForm J).conj = J.conj := by rfl

@[simp] public theorem standardForm_form (J : HermitianForm 3 F) :
    (standardForm J).form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by rfl

private theorem adjoint_mul (J : HermitianForm 3 F)
    (A B : Matrix (Fin 3) (Fin 3) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem adjoint_one (J : HermitianForm 3 F) :
    J.conjTranspose 1 = 1 := by
  change ((J.conj : F →+* F).mapMatrix 1).transpose = _
  rw [map_one, transpose_one]

private def adjointUnit (J : HermitianForm 3 F) (C : GL (Fin 3) F) : GL (Fin 3) F where
  val := J.conjTranspose C.val
  inv := J.conjTranspose (C⁻¹).val
  val_inv := by rw [← adjoint_mul]; simpa using adjoint_one J
  inv_val := by rw [← adjoint_mul]; simpa using adjoint_one J

private theorem conjugate_preserves_iff (J : HermitianForm 3 F) (C B : GL (Fin 3) F) :
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
public theorem special_conjugate_iff (J : HermitianForm 3 F) (C B : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form) :
    C * B * C⁻¹ ∈ J.specialSubgroup ↔ B ∈ (standardForm J).specialSubgroup := by
  rw [J.mem_specialSubgroup_iff, (standardForm J).mem_specialSubgroup_iff,
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

/-- The actual matrix conjugation equivalence from an arbitrary SU₃ to standard SU₃. -/
public def specialEquiv (J : HermitianForm 3 F) (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form) :
    J.specialSubgroup ≃* (standardForm J).specialSubgroup :=
  (restrictConjugation _ _ C (fun B => special_conjugate_iff J C B hC)).symm

@[simp] public theorem specialEquiv_apply (J : HermitianForm 3 F) (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)
    (A : J.specialSubgroup) :
    (specialEquiv J C hC A : GL (Fin 3) F) = C⁻¹ * A * C := by rfl

@[simp] public theorem specialEquiv_symm_apply (J : HermitianForm 3 F) (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)
    (A : (standardForm J).specialSubgroup) :
    ((specialEquiv J C hC).symm A : GL (Fin 3) F) = C * A * C⁻¹ := by rfl

/-- Conjugation descends along the genuine quotient map GL → PGL. -/
public theorem projective_conjugate_iff (J : HermitianForm 3 F) (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)
    (x : Matrix.ProjGenLinGroup (Fin 3) F) :
    ProjGenLinGroup.mk C * x * (ProjGenLinGroup.mk C)⁻¹ ∈
        ProjectiveSpecialUnitaryMatrixGroup J ↔
      x ∈ ProjectiveSpecialUnitaryMatrixGroup (standardForm J) := by
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

/-- Conjugation on PGL restricts to the actual PSU₃ images. -/
public def projectiveEquiv (J : HermitianForm 3 F) (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form) :
    ProjectiveSpecialUnitaryMatrixGroup J ≃*
      ProjectiveSpecialUnitaryMatrixGroup (standardForm J) :=
  (restrictConjugation _ _ (ProjGenLinGroup.mk C)
    (fun x => projective_conjugate_iff J C hC x)).symm

@[simp] public theorem projectiveEquiv_apply (J : HermitianForm 3 F) (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) :
    (projectiveEquiv J C hC x : ProjGenLinGroup (Fin 3) F) =
      (ProjGenLinGroup.mk C)⁻¹ * x * ProjGenLinGroup.mk C := by rfl

@[simp] public theorem projectiveEquiv_symm_apply (J : HermitianForm 3 F)
    (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)
    (x : ProjectiveSpecialUnitaryMatrixGroup (standardForm J)) :
    ((projectiveEquiv J C hC).symm x : ProjGenLinGroup (Fin 3) F) =
      ProjGenLinGroup.mk C * x * (ProjGenLinGroup.mk C)⁻¹ := by rfl

/-- Matrix and projective transport commute with the natural projection. -/
public theorem projectiveEquiv_mk (J : HermitianForm 3 F) (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)
    (A : J.specialSubgroup) :
    (projectiveEquiv J C hC
      ⟨ProjGenLinGroup.mk (A : GL (Fin 3) F), ⟨A, A.property, rfl⟩⟩ :
        ProjGenLinGroup (Fin 3) F) =
      ProjGenLinGroup.mk (specialEquiv J C hC A : GL (Fin 3) F) := by
  simp only [projectiveEquiv_apply, specialEquiv_apply, map_mul, map_inv]

/-- No basis or standard-form hypothesis is required, including when n = 1. -/
public theorem exists_standard_basis [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    ∃ C : GL (Fin 3) F,
      J.conjTranspose C.val * J.form * C.val = (standardForm J).form :=
  BenderSuzuki.External.huppert_II_10_4_b_standard_hermitian_basis J (2 ^ n)
    hcard (fixed_card J n hn hcard hconj)

/-- Simultaneous SU₃ and PSU₃ transport, with the invertible basis and both
conjugation formulas supplied from precisely the source field hypotheses. -/
public theorem exists_standard_transport [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    ∃ (C : GL (Fin 3) F)
      (e : J.specialSubgroup ≃* (standardForm J).specialSubgroup)
      (ep : ProjectiveSpecialUnitaryMatrixGroup J ≃*
        ProjectiveSpecialUnitaryMatrixGroup (standardForm J)),
      J.conjTranspose C.val * J.form * C.val = (standardForm J).form ∧
      (∀ A : J.specialSubgroup, (e A : GL (Fin 3) F) = C⁻¹ * A * C) ∧
      (∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
        (ep x : ProjGenLinGroup (Fin 3) F) =
          (ProjGenLinGroup.mk C)⁻¹ * x * ProjGenLinGroup.mk C) := by
  obtain ⟨C, hC⟩ := exists_standard_basis J n hn hcard hconj
  exact ⟨C, specialEquiv J C hC, projectiveEquiv J C hC, hC,
    specialEquiv_apply J C hC, projectiveEquiv_apply J C hC⟩

end CFSG.Quasithin.ChapterF.Source.Unitary.FormTransport

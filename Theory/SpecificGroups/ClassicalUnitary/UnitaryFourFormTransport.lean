module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
public import Theory.FieldTheory.QuadraticFrobeniusFixed
public import BenderSuzuki.External.Huppert.II.theorem_10_4

/-!
# Arbitrary-form transport for the four-dimensional unitary groups

Over a field of order q², q = 2^n with n positive, every nondegenerate
Hermitian form for x ↦ x^q is congruent to the existing antidiagonal form.
Normalize both forms to the identity and compose their basis matrices.
Conjugation identifies the special unitary matrix groups and their actual
images in PGL. In characteristic two the SU₄ projection is injective, so
local calculations may also be transported directly from standard SU₄.

Source: Huppert II.10.4 and the arbitrary Hermitian-form convention in
Aschbacher–Smith, Theorem 0.1.2(1), printed pp.4 and 482. The adjoint and
projective conjugation arguments adapt the existing SU₃ FormTransport proof;
the dimension-four normalization uses two orthonormal bases. All parameters
include n = 1. No local classification is asserted here.
-/

noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport
variable {F : Type*} [Field F]

/-- The existing antidiagonal form with the original stored involution. -/
public abbrev standardForm (J : HermitianForm 4 F) : HermitianForm 4 F :=
  UnitaryFourFlag.form F J.conj J.conj_involutive

private theorem adjoint_mul (J : HermitianForm 4 F)
    (A B : Matrix (Fin 4) (Fin 4) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem adjoint_one (J : HermitianForm 4 F) :
    J.conjTranspose 1 = 1 := by
  change ((J.conj : F →+* F).mapMatrix 1).transpose = _
  rw [map_one, transpose_one]

private def adjointUnit (J : HermitianForm 4 F) (C : GL (Fin 4) F) : GL (Fin 4) F where
  val := J.conjTranspose C.val
  inv := J.conjTranspose (C⁻¹).val
  val_inv := by rw [← adjoint_mul]; simpa using adjoint_one J
  inv_val := by rw [← adjoint_mul]; simpa using adjoint_one J

private theorem conjugate_preserves_iff (J : HermitianForm 4 F) (C B : GL (Fin 4) F) :
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
public theorem special_conjugate_iff (J : HermitianForm 4 F) (C B : GL (Fin 4) F)
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

/-- The actual matrix conjugation equivalence from an arbitrary SU₄ to standard SU₄. -/
public def specialEquiv (J : HermitianForm 4 F) (C : GL (Fin 4) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form) :
    J.specialSubgroup ≃* (standardForm J).specialSubgroup :=
  (restrictConjugation _ _ C (fun B => special_conjugate_iff J C B hC)).symm

@[simp] public theorem specialEquiv_apply (J : HermitianForm 4 F) (C : GL (Fin 4) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)
    (A : J.specialSubgroup) :
    (specialEquiv J C hC A : GL (Fin 4) F) = C⁻¹ * A * C := by rfl

@[simp] public theorem specialEquiv_symm_apply (J : HermitianForm 4 F) (C : GL (Fin 4) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)
    (A : (standardForm J).specialSubgroup) :
    ((specialEquiv J C hC).symm A : GL (Fin 4) F) = C * A * C⁻¹ := by rfl

/-- Conjugation descends along the genuine quotient map GL → PGL. -/
public theorem projective_conjugate_iff (J : HermitianForm 4 F) (C : GL (Fin 4) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)
    (x : Matrix.ProjGenLinGroup (Fin 4) F) :
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

/-- Conjugation on PGL restricts to the actual PSU₄ images. -/
public def projectiveEquiv (J : HermitianForm 4 F) (C : GL (Fin 4) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form) :
    ProjectiveSpecialUnitaryMatrixGroup J ≃*
      ProjectiveSpecialUnitaryMatrixGroup (standardForm J) :=
  (restrictConjugation _ _ (ProjGenLinGroup.mk C)
    (fun x => projective_conjugate_iff J C hC x)).symm

@[simp] public theorem projectiveEquiv_apply (J : HermitianForm 4 F) (C : GL (Fin 4) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) :
    (projectiveEquiv J C hC x : ProjGenLinGroup (Fin 4) F) =
      (ProjGenLinGroup.mk C)⁻¹ * x * ProjGenLinGroup.mk C := by rfl

@[simp] public theorem projectiveEquiv_symm_apply (J : HermitianForm 4 F)
    (C : GL (Fin 4) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)
    (x : ProjectiveSpecialUnitaryMatrixGroup (standardForm J)) :
    ((projectiveEquiv J C hC).symm x : ProjGenLinGroup (Fin 4) F) =
      ProjGenLinGroup.mk C * x * (ProjGenLinGroup.mk C)⁻¹ := by rfl

/-- Matrix and projective transport commute with the natural projection. -/
public theorem projectiveEquiv_mk (J : HermitianForm 4 F) (C : GL (Fin 4) F)
    (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)
    (A : J.specialSubgroup) :
    (projectiveEquiv J C hC
      ⟨ProjGenLinGroup.mk (A : GL (Fin 4) F), ⟨A, A.property, rfl⟩⟩ :
        ProjGenLinGroup (Fin 4) F) =
      ProjGenLinGroup.mk (specialEquiv J C hC A : GL (Fin 4) F) := by
  simp only [projectiveEquiv_apply, specialEquiv_apply, map_mul, map_inv]

/-- The stored involution has exactly `2^n` fixed elements. -/
public theorem fixed_card [Finite F] (J : HermitianForm 4 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    Nat.card {x : F // J.conj x = x} = 2 ^ n := by
  classical
  let K := GaloisField 2 (2 * n)
  let : Fintype F := Fintype.ofFinite F
  let : Fintype K := Fintype.ofFinite K
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul]
    congr 1
    omega
  let e : F ≃+* K := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hcard.trans hK.symm)
  let σ := iterateFrobeniusEquiv K 2 n
  have he (x : F) : J.conj x = x ↔ σ (e x) = e x := by
    rw [hconj, iterateFrobeniusEquiv_def, ← map_pow]
    exact e.injective.eq_iff.symm
  exact (Nat.card_congr (e.toEquiv.subtypeEquiv he)).trans
    (GaloisField.card_fixedBy_quadraticFrobenius 2 n (by omega))

/-- The source field cardinality supplies characteristic two, including `n = 1`. -/
public theorem charP_two [Finite F] (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) : CharP F 2 := by
  let : Fintype F := Fintype.ofFinite F
  apply ringChar.of_eq
  apply (FiniteField.even_card_iff_char_two).mpr
  rw [← Nat.card_eq_fintype_card, hcard]
  have he : Even (2 ^ n) := even_two.pow_of_ne_zero (by omega)
  exact Nat.mod_eq_zero_of_dvd
    (even_iff_two_dvd.mp (he.pow_of_ne_zero (by decide : (2 : ℕ) ≠ 0)))

/-- Two orthonormal bases give a change from any allowed form to the existing
antidiagonal form. No standard Gram matrix is assumed. -/
public theorem exists_standard_basis [Finite F] (J : HermitianForm 4 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    ∃ C : GL (Fin 4) F,
      J.conjTranspose C.val * J.form * C.val = (standardForm J).form := by
  have hfixed := fixed_card J n hn hcard hconj
  obtain ⟨P, hP⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    4 J (2 ^ n) hcard hfixed
  obtain ⟨Q, hQ⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    4 (standardForm J) (2 ^ n) hcard hfixed
  refine ⟨P * Q⁻¹, ?_⟩
  have hcancel : J.conjTranspose (Q⁻¹).val * J.conjTranspose Q.val = 1 := by
    rw [← adjoint_mul]
    simpa using adjoint_one J
  have hQ' : J.conjTranspose Q.val * (standardForm J).form * Q.val = 1 := hQ
  calc
    J.conjTranspose (P * Q⁻¹).val * J.form * (P * Q⁻¹).val =
        J.conjTranspose (Q⁻¹).val *
          (J.conjTranspose P.val * J.form * P.val) * (Q⁻¹).val := by
      simp only [Units.val_mul, adjoint_mul, mul_assoc]
    _ = J.conjTranspose (Q⁻¹).val * 1 * (Q⁻¹).val := by rw [hP]
    _ = J.conjTranspose (Q⁻¹).val *
        (J.conjTranspose Q.val * (standardForm J).form * Q.val) * (Q⁻¹).val := by
      rw [hQ']
    _ = (standardForm J).form := by
      simp only [← mul_assoc, hcancel, one_mul, Units.mul_inv_cancel_right]

/-- Simultaneous SU₄ and PSU₄ transport, with the invertible basis and both
conjugation formulas supplied from precisely the source field hypotheses. -/
public theorem exists_standard_transport [Finite F] (J : HermitianForm 4 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    ∃ (C : GL (Fin 4) F)
      (e : J.specialSubgroup ≃* (standardForm J).specialSubgroup)
      (ep : ProjectiveSpecialUnitaryMatrixGroup J ≃*
        ProjectiveSpecialUnitaryMatrixGroup (standardForm J)),
      J.conjTranspose C.val * J.form * C.val = (standardForm J).form ∧
      (∀ A : J.specialSubgroup, (e A : GL (Fin 4) F) = C⁻¹ * A * C) ∧
      (∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
        (ep x : ProjGenLinGroup (Fin 4) F) =
          (ProjGenLinGroup.mk C)⁻¹ * x * ProjGenLinGroup.mk C) := by
  obtain ⟨C, hC⟩ := exists_standard_basis J n hn hcard hconj
  exact ⟨C, specialEquiv J C hC, projectiveEquiv J C hC, hC,
    specialEquiv_apply J C hC, projectiveEquiv_apply J C hC⟩

/-- In characteristic two SU₄ maps isomorphically onto the actual PSU₄ image. -/
public def projectEquiv [Finite F] [CharP F 2] (J : HermitianForm 4 F) :
    J.specialSubgroup ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  MulEquiv.ofBijective (UnitaryFourFlag.project F J)
    ⟨UnitaryFourFlag.project_injective F J, UnitaryFourFlag.project_surjective F J⟩

/-- Every source PSU₄ carrier is isomorphic to the standard SU₄ matrix group
on the same field and with the same involution. -/
public theorem nonempty_projectiveEquiv_standardSU [Finite F] (J : HermitianForm 4 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃* (standardForm J).specialSubgroup) := by
  let : CharP F 2 := charP_two n hn hcard
  obtain ⟨C, hC⟩ := exists_standard_basis J n hn hcard hconj
  exact ⟨(projectiveEquiv J C hC).trans (projectEquiv (standardForm J)).symm⟩

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport

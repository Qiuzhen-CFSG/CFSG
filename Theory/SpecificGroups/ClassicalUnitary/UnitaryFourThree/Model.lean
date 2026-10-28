module

public import Theory.LinearAlgebra.Hermitian.PrimeFrobeniusNormalization
public import Theory.FieldTheory.Nine
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Field-nine projective unitary models and arbitrary-form transport

An orthonormal basis conjugates an arbitrary nondegenerate Hermitian form
with cube conjugation to the identity form. An equivalence of the coefficient
field with `FiniteField.Nine` then acts entrywise on matrices. Both maps descend
through GL modulo its center and restrict to the actual SU images in PGL.
Thus this construction retains the scalar kernel in odd characteristic.

The dimension remains general so that the dimension-three sections and the
ambient dimension-four group use compatible concrete carriers. Only model
transport and finiteness are asserted here; no subgroup classification is assumed.

Sources: Huppert II.10.4, formalized in `PrimeFrobeniusNormalization`, and
Aschbacher–Smith, Theorem 0.1.2(4), printed p.4 of `refs/quasithin.pdf`.
The adjoint calculation adapts the repository's dimension-three
`RankOneBorels/Unitary/FormTransport.lean` to arbitrary dimension.
-/

open Matrix BenderSuzuki.MatrixGroups

public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

variable {n : ℕ} {F E : Type*} [Field F] [Field E]

/-- The identity Gram matrix with the supplied involution. -/
@[expose] def identityForm (σ : F ≃+* F) (hσ : Function.Involutive σ) : HermitianForm n F where
  conj := σ
  conj_involutive := hσ
  form := 1
  form_hermitian := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, Ne.symm]
  form_nondegenerate := by simp

private theorem adjoint_mul (J : HermitianForm n F)
    (A B : Matrix (Fin n) (Fin n) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem adjoint_one (J : HermitianForm n F) : J.conjTranspose 1 = 1 := by
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

/-- A change of orthonormal basis preserves SU, including determinant one. -/
theorem special_conjugate_iff (J : HermitianForm n F) (C B : GL (Fin n) F)
    (hC : J.conjTranspose C.val * J.form * C.val = 1) :
    C * B * C⁻¹ ∈ J.specialSubgroup ↔
      B ∈ (identityForm (n := n) J.conj J.conj_involutive).specialSubgroup := by
  rw [J.mem_specialSubgroup_iff,
    (identityForm (n := n) J.conj J.conj_involutive).mem_specialSubgroup_iff,
    conjugate_preserves_iff, hC]
  simp only [map_mul, map_inv, mul_assoc, mul_mul_inv_cancel'_right]
  rfl

private def restrictEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (U : Subgroup G) (V : Subgroup H)
    (h : ∀ x, e x ∈ V ↔ x ∈ U) : U ≃* V where
  toFun x := ⟨e x, (h x).2 x.property⟩
  invFun x := ⟨e.symm x, (h _).1 (by simp)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp

/-- A GL equivalence carries the actual PSU images when it carries SU. -/
def projectiveEquivOfGL (J : HermitianForm n F) (K : HermitianForm n E)
    (e : GL (Fin n) F ≃* GL (Fin n) E)
    (h : ∀ x, e x ∈ K.specialSubgroup ↔ x ∈ J.specialSubgroup) :
    ProjectiveSpecialUnitaryMatrixGroup J ≃* ProjectiveSpecialUnitaryMatrixGroup K := by
  have hz : (Subgroup.center (GL (Fin n) F)).map e.toMonoidHom =
      Subgroup.center (GL (Fin n) E) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Subgroup.centerCongr e ⟨x, hx⟩).property
    · intro hy
      exact ⟨e.symm y, (Subgroup.centerCongr e.symm ⟨y, hy⟩).property,
        e.apply_symm_apply y⟩
  let ep : ProjGenLinGroup (Fin n) F ≃* ProjGenLinGroup (Fin n) E :=
    QuotientGroup.congr _ _ e hz
  have hep (x : GL (Fin n) F) : ep (ProjGenLinGroup.mk x) = ProjGenLinGroup.mk (e x) :=
    QuotientGroup.congr_mk _ _ e hz x
  apply restrictEquiv ep _ _
  intro x
  constructor
  · rintro ⟨a, ha, hax⟩
    refine ⟨e.symm a, (h _).1 (by simpa using ha), ?_⟩
    apply ep.injective
    rw [hep, e.apply_symm_apply, hax]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨e a, (h a).2 ha, (hep a).symm⟩

/-- Orthogonalization descends to the defining image in PGL. -/
def projectiveBasisEquiv (J : HermitianForm n F) (C : GL (Fin n) F)
    (hC : J.conjTranspose C.val * J.form * C.val = 1) :
    ProjectiveSpecialUnitaryMatrixGroup J ≃*
      ProjectiveSpecialUnitaryMatrixGroup (identityForm (n := n) J.conj J.conj_involutive) :=
  (projectiveEquivOfGL _ _ (MulAut.conj C)
    (fun B => special_conjugate_iff J C B hC)).symm

/-- Entrywise field transport on invertible matrices. -/
def coefficientGL (e : F ≃+* E) : GL (Fin n) F ≃* GL (Fin n) E :=
  { GeneralLinearGroup.map e.toRingHom with
    invFun := GeneralLinearGroup.map e.symm.toRingHom
    left_inv := by intro g; ext i j; exact e.symm_apply_apply (g i j)
    right_inv := by intro g; ext i j; exact e.apply_symm_apply (g i j) }

/-- Transport between identity Hermitian models with compatible involutions. -/
def projectiveCoefficientEquiv (e : F ≃+* E)
    (σ : F ≃+* F) (hσ : Function.Involutive σ)
    (τ : E ≃+* E) (hτ : Function.Involutive τ)
    (hc : ∀ x, e (σ x) = τ (e x)) :
    ProjectiveSpecialUnitaryMatrixGroup (identityForm (n := n) σ hσ) ≃*
      ProjectiveSpecialUnitaryMatrixGroup (identityForm (n := n) τ hτ) := by
  apply projectiveEquivOfGL _ _ (coefficientGL e)
  intro x
  rw [HermitianForm.mem_specialSubgroup_iff, HermitianForm.mem_specialSubgroup_iff]
  have hadj : (identityForm (n := n) τ hτ).conjTranspose (coefficientGL e x).val =
      ((identityForm (n := n) σ hσ).conjTranspose x.val).map e := by
    ext i j
    exact (hc (x.val j i)).symm
  have hval : (coefficientGL e x).val = x.val.map e := rfl
  have hu :
      (identityForm (n := n) τ hτ).conjTranspose (coefficientGL e x).val *
          (identityForm (n := n) τ hτ).form * (coefficientGL e x).val =
        (identityForm (n := n) τ hτ).form ↔
      (identityForm (n := n) σ hσ).conjTranspose x.val *
          (identityForm (n := n) σ hσ).form * x.val =
        (identityForm (n := n) σ hσ).form := by
    change _ * 1 * _ = 1 ↔ _ * 1 * _ = 1
    rw [hadj, hval, mul_one, mul_one, ← Matrix.map_mul]
    constructor
    · intro hh
      ext i j
      apply e.injective
      simpa only [Matrix.map_apply, Matrix.one_apply, apply_ite, map_one, map_zero] using
        congrArg (fun A => A i j) hh
    · intro hh
      rw [hh]
      exact Matrix.map_one e (map_zero e) (map_one e)
  rw [hu]
  apply and_congr_right
  intro _
  change GeneralLinearGroup.det (GeneralLinearGroup.map e.toRingHom x) = 1 ↔ _
  rw [GeneralLinearGroup.map_det]
  constructor
  · intro hh
    apply Units.ext
    apply e.injective
    simpa using congrArg Units.val hh
  · intro hh
    rw [hh, map_one]

@[expose] def conjugation : FiniteField.Nine ≃+* FiniteField.Nine :=
  { starRingEnd FiniteField.Nine with
    invFun := star
    left_inv := star_involutive
    right_inv := star_involutive }

/-- The concrete field-nine model in each dimension; dimension four is the consumer. -/
@[expose] def form (n : ℕ) : HermitianForm n FiniteField.Nine :=
  identityForm conjugation star_involutive

abbrev Carrier (n : ℕ) := ProjectiveSpecialUnitaryMatrixGroup (form n)

instance carrierFinite (n : ℕ) : Finite (Carrier n) := by
  let : Finite (GL (Fin n) FiniteField.Nine) :=
    Finite.of_injective Units.val Units.val_injective
  let p : (form n).specialSubgroup →* Carrier n :=
    (ProjGenLinGroup.mk.comp (form n).specialSubgroup.subtype).codRestrict _
      (fun a => ⟨a.val, a.property, rfl⟩)
  apply Finite.of_surjective p
  rintro ⟨x, a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩

/-- Every allowed field-nine Hermitian model is actually isomorphic to the fixed model. -/
theorem exists_model_equiv [Finite F] (J : HermitianForm n F)
    (hcard : Nat.card F = 9) (hc : ∀ x, J.conj x = x ^ 3) :
    Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃* Carrier n) := by
  let : Fintype F := Fintype.ofFinite F
  let e : F ≃+* FiniteField.Nine := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, FiniteField.Nine.natCard] using hcard)
  let : CharP F 3 := charP_of_card_eq_prime_pow (p := 3) (f := 2) (by
    simpa [← Nat.card_eq_fintype_card] using hcard)
  obtain ⟨C, hC⟩ := J.exists_orthonormal_basis_of_prime_frobenius hc (by
    simpa using hcard)
  refine ⟨(projectiveBasisEquiv J C hC).trans
    (projectiveCoefficientEquiv e J.conj J.conj_involutive
      conjugation star_involutive ?_)⟩
  intro x
  change e (J.conj x) = star (e x)
  rw [hc, map_pow, FiniteField.Nine.star_eq_cube]

/-- The stored involution on the fixed carrier is exactly cube Frobenius. -/
theorem form_conj_cube (n : ℕ) (x : FiniteField.Nine) :
    (form n).conj x = x ^ 3 := FiniteField.Nine.star_eq_cube x

/-- The standard Gram matrix is the identity. -/
theorem form_gram (n : ℕ) : (form n).form = 1 := rfl

/-- Projection onto the actual projective image. -/
@[expose] def project (n : ℕ) : (form n).specialSubgroup →* Carrier n :=
  (ProjGenLinGroup.mk.comp (form n).specialSubgroup.subtype).codRestrict _
    (fun a => ⟨a.val, a.property, rfl⟩)

theorem project_surjective (n : ℕ) : Function.Surjective (project n) := by
  rintro ⟨x, a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩

/-- Reducibility uses the full inverse image of the projective subgroup in SU.
The vectors carry its defining matrix action, not an assumed PSU linear action. -/
@[expose] def IsReducible (U : Subgroup (Carrier 4)) : Prop :=
  ∃ W : Submodule FiniteField.Nine (Fin 4 → FiniteField.Nine),
    W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ g : (form 4).specialSubgroup, project 4 g ∈ U →
        ∀ v ∈ W, g.val.val.mulVec v ∈ W

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

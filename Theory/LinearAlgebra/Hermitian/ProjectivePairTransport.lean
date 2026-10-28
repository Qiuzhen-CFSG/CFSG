module

public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Simultaneous transport of projective unitary groups and their special subgroups

Nondegenerate Hermitian forms over finite fields with the same matrix-field
and fixed-field orders have isomorphic projective unitary pairs PSU ≤ PGU.
Orthonormal bases and a coefficient-field isomorphism give a single GL
equivalence preserving both the unitary and determinant-one conditions.
Quotienting by the actual GL centers gives a single PGL equivalence preserving
both images, so the resulting identifications respect their inclusions.

This extends the special-group transport in `FiniteFieldEquivalence` to the
full projective unitary group, keeping the special image distinguished.
Source: Huppert II.10.4, as proved in
`BenderSuzuki/External/Huppert/II/theorem_10_4.lean`.
-/

open Matrix BenderSuzuki.MatrixGroups

public noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm.ProjectivePairTransport

variable {F E : Type*} [Field F] [Field E] {n : ℕ}

private theorem adjoint_mul (J : HermitianForm n F)
    (A B : Matrix (Fin n) (Fin n) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private def adjointUnit (J : HermitianForm n F) (C : GL (Fin n) F) : GL (Fin n) F where
  val := J.conjTranspose C.val
  inv := J.conjTranspose (C⁻¹).val
  val_inv := by
    rw [← adjoint_mul, Units.inv_mul]
    change ((J.conj : F →+* F).mapMatrix 1).transpose = 1
    rw [map_one, transpose_one]
  inv_val := by
    rw [← adjoint_mul, Units.mul_inv]
    change ((J.conj : F →+* F).mapMatrix 1).transpose = 1
    rw [map_one, transpose_one]

/-- An orthonormal basis transports the full unitary condition. -/
theorem unitary_conjugate_iff (J : HermitianForm n F) (C B : GL (Fin n) F)
    (hC : J.conjTranspose C.val * J.form * C.val = 1) :
    C * B * C⁻¹ ∈ J.unitarySubgroup ↔ B ∈ (IdentityGram.identityGram J).unitarySubgroup := by
  rw [J.mem_unitarySubgroup_iff, HermitianForm.mem_unitarySubgroup_iff]
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
  change _ ↔ J.conjTranspose B.val * 1 * B.val = 1
  rw [← hC, he]
  change _ ↔ (adjointUnit J C).val * _ * C.val =
    (adjointUnit J C).val * J.form * C.val
  rw [Units.mul_left_inj, Units.mul_right_inj]

private def coefficientGL (e : F ≃+* E) : GL (Fin n) F ≃* GL (Fin n) E :=
  { GeneralLinearGroup.map e.toRingHom with
    invFun := GeneralLinearGroup.map e.symm.toRingHom
    left_inv := by intro g; ext i j; exact e.symm_apply_apply (g i j)
    right_inv := by intro g; ext i j; exact e.apply_symm_apply (g i j) }

private theorem coefficient_unitary_iff (e : F ≃+* E)
    (J : HermitianForm n F) (K : HermitianForm n E)
    (hc : ∀ x, e (J.conj x) = K.conj (e x))
    (hform : J.form.map e = K.form) (x : GL (Fin n) F) :
    coefficientGL e x ∈ K.unitarySubgroup ↔ x ∈ J.unitarySubgroup := by
  rw [K.mem_unitarySubgroup_iff, J.mem_unitarySubgroup_iff]
  have hadj : K.conjTranspose (coefficientGL e x).val =
      (J.conjTranspose x.val).map e := by
    ext i j
    exact (hc (x.val j i)).symm
  have hval : (coefficientGL e x).val = x.val.map e := rfl
  rw [hadj, hval, ← hform, ← Matrix.map_mul, ← Matrix.map_mul]
  exact e.toEquiv.mapMatrix.injective.eq_iff

private theorem coefficient_special_iff (e : F ≃+* E)
    (J : HermitianForm n F) (K : HermitianForm n E)
    (hc : ∀ x, e (J.conj x) = K.conj (e x))
    (hform : J.form.map e = K.form) (x : GL (Fin n) F) :
    coefficientGL e x ∈ K.specialSubgroup ↔ x ∈ J.specialSubgroup := by
  change (_ ∈ K.unitarySubgroup ∧ _) ↔ (_ ∈ J.unitarySubgroup ∧ _)
  rw [coefficient_unitary_iff e J K hc hform]
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

private def projectiveGL (e : GL (Fin n) F ≃* GL (Fin n) E) :
    ProjGenLinGroup (Fin n) F ≃* ProjGenLinGroup (Fin n) E :=
  QuotientGroup.congr _ _ e (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Subgroup.centerCongr e ⟨x, hx⟩).property
    · intro hy
      exact ⟨e.symm y, (Subgroup.centerCongr e.symm ⟨y, hy⟩).property,
        e.apply_symm_apply y⟩)

private theorem projectiveGL_mk (e : GL (Fin n) F ≃* GL (Fin n) E)
    (x : GL (Fin n) F) :
    projectiveGL e (ProjGenLinGroup.mk x) = ProjGenLinGroup.mk (e x) := rfl

private theorem projectiveGL_mem_map_iff (e : GL (Fin n) F ≃* GL (Fin n) E)
    (H : Subgroup (GL (Fin n) F)) (K : Subgroup (GL (Fin n) E))
    (h : ∀ x, e x ∈ K ↔ x ∈ H) (x : ProjGenLinGroup (Fin n) F) :
    projectiveGL e x ∈ K.map ProjGenLinGroup.mk ↔ x ∈ H.map ProjGenLinGroup.mk := by
  constructor
  · rintro ⟨a, ha, hax⟩
    refine ⟨e.symm a, (h _).1 (by simpa using ha), ?_⟩
    apply (projectiveGL e).injective
    rw [projectiveGL_mk, e.apply_symm_apply, hax]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨e a, (h a).2 ha, (projectiveGL_mk e a).symm⟩

/-- One equivalence of the ambient PGL groups carries both PGU and PSU.
The two membership equivalences refer to the same map. -/
theorem exists_projective_pair_equiv_of_card [Finite F] [Finite E]
    (J : HermitianForm n F) (K : HermitianForm n E) (q : ℕ)
    (hF : Nat.card F = q ^ 2) (hJ : Nat.card {x : F // J.conj x = x} = q)
    (hE : Nat.card E = q ^ 2) (hK : Nat.card {x : E // K.conj x = x} = q) :
    ∃ e : ProjGenLinGroup (Fin n) F ≃* ProjGenLinGroup (Fin n) E,
      (∀ x, e x ∈ K.unitarySubgroup.map ProjGenLinGroup.mk ↔
        x ∈ J.unitarySubgroup.map ProjGenLinGroup.mk) ∧
      (∀ x, e x ∈ ProjectiveSpecialUnitaryMatrixGroup K ↔
        x ∈ ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype E := Fintype.ofFinite E
  let f : F ≃+* E := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hF.trans hE.symm)
  obtain ⟨C, hC⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis n J q hF hJ
  obtain ⟨D, hD⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis n K q hE hK
  have hc (x : F) : f ((IdentityGram.identityGram J).conj x) =
      (IdentityGram.identityGram K).conj (f x) := by
    change f (J.conj x) = K.conj (f x)
    rw [BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J q hF hJ,
      BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius K q hE hK, map_pow]
  have hf : (IdentityGram.identityGram J).form.map f =
      (IdentityGram.identityGram K).form := by simp
  let e := (MulAut.conj C⁻¹).trans ((coefficientGL f).trans (MulAut.conj D))
  have hu (x : GL (Fin n) F) : e x ∈ K.unitarySubgroup ↔ x ∈ J.unitarySubgroup := by
    change D * coefficientGL f (C⁻¹ * x * (C⁻¹)⁻¹) * D⁻¹ ∈ _ ↔ _
    rw [unitary_conjugate_iff K D _ hD,
      coefficient_unitary_iff f _ _ hc hf, ← unitary_conjugate_iff J C _ hC]
    simp [mul_assoc]
  have hs (x : GL (Fin n) F) : e x ∈ K.specialSubgroup ↔ x ∈ J.specialSubgroup := by
    change D * coefficientGL f (C⁻¹ * x * (C⁻¹)⁻¹) * D⁻¹ ∈ _ ↔ _
    rw [IdentityGram.special_conjugate_iff K D _ hD,
      coefficient_special_iff f _ _ hc hf, ← IdentityGram.special_conjugate_iff J C _ hC]
    simp [mul_assoc]
  exact ⟨projectiveGL e, projectiveGL_mem_map_iff e _ _ hu,
    projectiveGL_mem_map_iff e _ _ hs⟩

end BenderSuzuki.MatrixGroups.HermitianForm.ProjectivePairTransport

module
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.SymmetricSimilarity
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.SemilinearReduction
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model

/-!
# Identity-Gram normalization preserving the projective unitary graph action

Finite-field ternary symmetric-form similarity supplies a matrix C fixed by
Hermitian conjugation, with CᵀC a nonzero scalar multiple of the antidiagonal
form. Conjugation by C carries the actual projective SU image to identity
Gram; the scalar cancels in the isometry equation. Since C is fixed, this
transport commutes with the entrywise graph action. On identity Gram its
special-unitary lift is literally inverse transpose.

Using similarity is essential: over the prime field p ≡ 3 modulo 4 the
two displayed Gram matrices need not be isometric. Source: GLS3 §§2.7,4.3,
and Aschbacher–Smith F.6.18(11), printed p.310.
-/

public noncomputable section
open Matrix BenderSuzuki.MatrixGroups Subgroup
namespace Theory.SpecificGroups.SU3.UnitaryGraphGram
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open HermitianForm.OddPrimeSylow.NormalizedOuter
variable {F : Type*} [Field F]

private theorem adjoint_mul (J : HermitianForm 3 F)
    (A B : Matrix (Fin 3) (Fin 3) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem adjoint_one (J : HermitianForm 3 F) : J.conjTranspose 1 = 1 := by
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

private theorem special_similarity_iff (J : HermitianForm 3 F)
    (C : GL (Fin 3) F) (a : F) (ha : a ≠ 0)
    (hC : J.conjTranspose C.val * C.val = a • J.form) (B : GL (Fin 3) F) :
    C * B * C⁻¹ ∈ (identityForm (n := 3) J.conj J.conj_involutive).specialSubgroup ↔
      B ∈ J.specialSubgroup := by
  let I := identityForm (n := 3) J.conj J.conj_involutive
  rw [I.mem_specialSubgroup_iff, J.mem_specialSubgroup_iff,
    conjugate_preserves_iff]
  have hgram : I.conjTranspose C.val * I.form * C.val = a • J.form := by
    change J.conjTranspose C.val * 1 * C.val = _
    simpa only [mul_one] using hC
  rw [hgram, mul_smul_comm, smul_mul_assoc]
  constructor
  · rintro ⟨hu, hd⟩
    refine ⟨?_, ?_⟩
    · change a • (J.conjTranspose B.val * J.form * B.val) = a • J.form at hu
      apply_fun (fun M : Matrix (Fin 3) (Fin 3) F => a⁻¹ • M) at hu
      simpa only [I, identityForm, HermitianForm.conjTranspose, smul_smul, inv_mul_cancel₀ ha, one_smul] using hu
    · simpa only [map_mul, map_inv, mul_assoc, mul_mul_inv_cancel'_right] using hd
  · rintro ⟨hu, hd⟩
    exact ⟨congrArg (a • ·) hu, by
      simpa only [map_mul, map_inv, mul_assoc, mul_mul_inv_cancel'_right] using hd⟩

private def projectiveSimilarity (J : HermitianForm 3 F)
    (C : GL (Fin 3) F) (a : F) (ha : a ≠ 0)
    (hC : J.conjTranspose C.val * C.val = a • J.form) :
    ProjectiveSpecialUnitaryMatrixGroup J ≃*
      ProjectiveSpecialUnitaryMatrixGroup (identityForm (n := 3) J.conj J.conj_involutive) :=
  by
  let I := identityForm (n := 3) J.conj J.conj_involutive
  have hiff (x : ProjGenLinGroup (Fin 3) F) :
      ProjGenLinGroup.mk C * x * (ProjGenLinGroup.mk C)⁻¹ ∈
        ProjectiveSpecialUnitaryMatrixGroup I ↔ x ∈ ProjectiveSpecialUnitaryMatrixGroup J := by
    constructor
    · rintro ⟨A, hA, hAx⟩
      refine ⟨C⁻¹ * A * C, ?_, ?_⟩
      · apply (special_similarity_iff J C a ha hC _).1
        simpa only [I, SetLike.mem_coe, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right, mul_inv_cancel, mul_one] using hA
      · simp only [map_mul, map_inv]
        rw [hAx]
        group
    · rintro ⟨A, hA, rfl⟩
      exact ⟨C * A * C⁻¹, (special_similarity_iff J C a ha hC A).2 hA,
        by simp only [map_mul, map_inv]⟩
  exact {
    toFun := fun x => ⟨ProjGenLinGroup.mk C * x.val * (ProjGenLinGroup.mk C)⁻¹,
      (hiff x.val).2 x.property⟩
    invFun := fun x => ⟨(ProjGenLinGroup.mk C)⁻¹ * x.val * ProjGenLinGroup.mk C,
      (hiff _).1 (by simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right, mul_inv_cancel, mul_one] using x.property)⟩
    left_inv := fun x => by apply Subtype.ext; dsimp; group
    right_inv := fun x => by apply Subtype.ext; dsimp; group
    map_mul' := fun x y => by apply Subtype.ext; dsimp; group }

private theorem projectiveSimilarity_val (J : HermitianForm 3 F)
    (C : GL (Fin 3) F) (a : F) (ha : a ≠ 0)
    (hC : J.conjTranspose C.val * C.val = a • J.form)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) :
    (projectiveSimilarity J C a ha hC x).val =
      ProjGenLinGroup.mk C * x.val * (ProjGenLinGroup.mk C)⁻¹ := by
  rfl

/-- Fixed-field similarity preserves the specified entrywise action while
replacing antidiagonal Gram by identity Gram. -/
theorem identity_gram_entrywise [Finite F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (hcard : Nat.card F = p ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = p)
    (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hγ : J.IsEntrywiseConjugation γ) :
    ∃ e : ProjectiveSpecialUnitaryMatrixGroup J ≃*
      ProjectiveSpecialUnitaryMatrixGroup (identityForm (n := 3) J.conj J.conj_involutive),
      (identityForm (n := 3) J.conj J.conj_involutive).IsEntrywiseConjugation (MulAut.congr e γ) := by
  obtain ⟨a, C, ha, _, hfixedC, hC⟩ := Descent.fixed_symmetric_ternary_similarity
    J hp hp8 hcard hfixed hJ 1 (by simp) (by simp) (by simp)
  have hC' : J.conjTranspose C.val * C.val = a • J.form := by
    change (C.val.map J.conj).transpose * C.val = _
    simpa only [hfixedC, mul_one] using hC
  let e := projectiveSimilarity J C a ha hC'
  let I := identityForm (n := 3) J.conj J.conj_involutive
  have he (x : ProjectiveSpecialUnitaryMatrixGroup J) :
      (e x).val = ProjGenLinGroup.mk C * x.val * (ProjGenLinGroup.mk C)⁻¹ :=
    projectiveSimilarity_val J C a ha hC' x
  have hfixP : ProjGenLinGroup.map J.conj.toRingHom (ProjGenLinGroup.mk C) =
      ProjGenLinGroup.mk C := by
    rw [ProjGenLinGroup.map_mk]
    exact congrArg ProjGenLinGroup.mk (Units.ext hfixedC)
  have hact (b : ProjectiveSpecialUnitaryMatrixGroup I) :
      ((MulAut.congr e γ) b).val = ProjGenLinGroup.map J.conj.toRingHom b.val := by
    obtain ⟨b, rfl⟩ := e.surjective b
    change (e (γ (e.symm (e b)))).val = _
    rw [e.symm_apply_apply, he, hγ.apply_val, he, map_mul, map_mul, map_inv, hfixP]
  refine ⟨e, ?_⟩
  intro x
  have hmem : GeneralLinearGroup.map J.conj.toRingHom x.val ∈ I.specialSubgroup := by
    obtain ⟨hx, hd⟩ := (I.mem_specialSubgroup_iff _).mp x.property
    apply (I.mem_specialSubgroup_iff _).mpr
    constructor
    · have hx' : (x.val.val.map J.conj).transpose * x.val.val = 1 := by
        change (x.val.val.map J.conj).transpose * 1 * x.val.val = 1 at hx
        simpa only [mul_one] using hx
      have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M.map J.conj) hx'
      have h1 : (1 : Matrix (Fin 3) (Fin 3) F).map J.conj = 1 := by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      change ((x.val.val.map J.conj).map J.conj).transpose * 1 *
        (x.val.val.map J.conj) = 1
      simpa only [Matrix.map_mul, Matrix.transpose_map, h1, mul_one] using hh
    · apply Units.ext
      change (J.conj.mapMatrix x.val.val).det = 1
      rw [← RingEquiv.map_det]
      have hd' : x.val.val.det = 1 := congrArg Units.val hd
      rw [hd', map_one]
  refine ⟨⟨GeneralLinearGroup.map J.conj.toRingHom x.val, hmem⟩, rfl, ?_⟩
  apply Subtype.ext
  rw [hact, I.specialToProjective_apply_val, ProjGenLinGroup.map_mk,
    I.specialToProjective_apply_val]


/-- On identity Gram, the special entrywise lift is literally inverse transpose. -/
theorem entrywise_lift_inverse_transpose (J : HermitianForm 3 F) (hJ : J.form = 1)
    (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hγ : J.IsEntrywiseConjugation γ) (x : J.specialSubgroup) :
    (HermitianForm.OddPrimeSylow.specialEntrywiseAut J hγ x).val.val = x.val.inv.transpose := by
  rw [HermitianForm.OddPrimeSylow.specialEntrywiseAut_val]
  have hx := (J.mem_specialSubgroup_iff _).mp x.property |>.1
  rw [hJ, mul_one] at hx
  have hu : adjointUnit J x.val * x.val = 1 := Units.ext hx
  have hinv : adjointUnit J x.val = x.val⁻¹ := mul_eq_one_iff_eq_inv.mp hu
  have hh := congrArg (fun A : GL (Fin 3) F => A.val.transpose) hinv
  change ((x.val.val.map J.conj).transpose).transpose = x.val.inv.transpose at hh
  simpa only [Matrix.transpose_transpose] using hh

end Theory.SpecificGroups.SU3.UnitaryGraphGram

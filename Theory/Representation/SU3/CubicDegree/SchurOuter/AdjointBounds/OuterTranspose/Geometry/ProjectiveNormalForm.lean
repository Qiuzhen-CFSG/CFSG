module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.Geometry.Coordinates
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.Descent
public import Theory.SpecificGroups.SU3.ProjectiveGraphFixed
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Natural matrix coordinates for outer involutions of PSU₃

Every non-inner involution of the actual projective special unitary image over
F of order `(2^s)^2`, with the stored conjugation `x ↦ x^(2^s)` and `s ≥ 2`,
admits the literal inverse-transpose coordinates specified in `Coordinates`.

First choose a standard antidiagonal Hermitian basis P. The unitary-semilinear
normal form and projective descent supply a unitary conjugator v. Retain v
in the matrix basis: the fixed matrix R with rows `[1,0,1]`, `[1,1,1]`,
`[0,1,1]` changes the antidiagonal form to the identity in characteristic two.
The resulting coordinates are P v R. The unitary equation then identifies
entrywise field conjugation with inverse transpose, and the literal PGL
projection equations transport the result back to the original form.

Source: GM04, Proposition 4.11, internal pp.31--32 (the SU₃ graph case);
GLS III, 2.5.12, 2.7, and 4.9.2. This is the group-only coordinate input for
the adjoint graph construction; it assumes no representation or intertwiner.
-/

public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
namespace Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.Geometry
variable {F : Type*} [Field F]

private def orthonormalBasis : GL (Fin 3) F :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0, 1; 1, 1, 1; 0, 1, 1]
    (by simp [Matrix.det_fin_three])

private theorem orthonormalBasis_fixed (J : HermitianForm 3 F) :
    GeneralLinearGroup.map J.conj.toRingHom (orthonormalBasis (F := F)) =
      orthonormalBasis := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [orthonormalBasis, GeneralLinearGroup.mkOfDetNeZero]

private theorem orthonormalBasis_gram [CharP F 2] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    J.conjTranspose (orthonormalBasis (F := F)).val * J.form *
      (orthonormalBasis (F := F)).val = 1 := by
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orthonormalBasis, GeneralLinearGroup.mkOfDetNeZero, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

private theorem adjoint_mul (J : HermitianForm 3 F)
    (A B : Matrix (Fin 3) (Fin 3) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem conjugation_eq_inverseTranspose (J : HermitianForm 3 F)
    (R B : GL (Fin 3) F)
    (hR : J.conjTranspose R.val * J.form * R.val = 1)
    (hB : J.conjTranspose B.val * J.form * B.val = J.form) :
    GeneralLinearGroup.map J.conj.toRingHom (R⁻¹ * B * R) =
      inverseTranspose (R⁻¹ * B * R) := by
  let A := R⁻¹ * B * R
  have hRA : R.val * A.val = B.val * R.val := by
    change (R * A).val = (B * R).val
    simp [A, mul_assoc]
  have hAR : J.conjTranspose A.val * J.conjTranspose R.val =
      J.conjTranspose R.val * J.conjTranspose B.val := by
    simpa only [adjoint_mul] using congrArg J.conjTranspose hRA
  have hA : J.conjTranspose A.val * A.val = 1 := by
    calc
      J.conjTranspose A.val * A.val =
          J.conjTranspose A.val * (J.conjTranspose R.val * J.form * R.val) * A.val := by
        rw [hR, mul_one]
      _ = (J.conjTranspose A.val * J.conjTranspose R.val) * J.form *
          (R.val * A.val) := by simp only [mul_assoc]
      _ = (J.conjTranspose R.val * J.conjTranspose B.val) * J.form *
          (B.val * R.val) := by rw [hAR, hRA]
      _ = J.conjTranspose R.val * (J.conjTranspose B.val * J.form * B.val) * R.val := by
        simp only [mul_assoc]
      _ = 1 := by rw [hB, hR]
  have hi : J.conjTranspose A.val = (A⁻¹).val := by
    apply (Units.mul_left_inj A).mp
    exact hA.trans (Units.inv_mul A).symm
  apply Units.ext
  change A.val.map J.conj = (A⁻¹).val.transpose
  change (A.val.map J.conj).transpose = (A⁻¹).val at hi
  simpa only [Matrix.transpose_transpose] using congrArg Matrix.transpose hi

private theorem standard_coordinates [CharP F 2] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ) (v : J.unitarySubgroup)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hv : MulAut.congr (J.unitaryConj v) γ = a) :
    HasProjectiveTransposeCoordinates J a := by
  let R := orthonormalBasis (F := F)
  refine ⟨v.val * R, fun g => ?_⟩
  let b := J.specialUnitaryConj v⁻¹ g
  have hb : J.unitaryConj v (J.specialToProjective b) = J.specialToProjective g := by
    rw [J.unitaryConj_specialToProjective]
    congr 1
    apply Subtype.ext
    simp [b, J.specialUnitaryConj_val, mul_assoc]
  have h := DFunLike.congr_fun hv (J.unitaryConj v (J.specialToProjective b))
  change J.unitaryConj v (γ ((J.unitaryConj v).symm
      (J.unitaryConj v (J.specialToProjective b)))) =
    a (J.unitaryConj v (J.specialToProjective b)) at h
  rw [MulEquiv.symm_apply_apply, hb] at h
  have hp := congrArg Subtype.val h
  rw [J.unitaryConj_apply_val, hγ.apply_val, J.specialToProjective_apply_val,
    ProjGenLinGroup.map_mk] at hp
  have hm : R⁻¹ * b.val * R = (v.val * R)⁻¹ * g.val * (v.val * R) := by
    simp [b, J.specialUnitaryConj_val, mul_assoc]
  have ht := conjugation_eq_inverseTranspose J R b.val
    (orthonormalBasis_gram J hJ) ((J.mem_specialSubgroup_iff _).mp b.property).1
  rw [← hm, ← ht, ← hp]
  have hR : GeneralLinearGroup.map J.conj.toRingHom R = R := orthonormalBasis_fixed J
  simp only [map_mul, map_inv, hR]
  simp only [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]

private theorem coordinates_transport (J : HermitianForm 3 F) (P : GL (Fin 3) F)
    (hP : J.conjTranspose P.val * J.form * P.val = (standardForm J).form)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : HasProjectiveTransposeCoordinates (standardForm J)
      (MulAut.congr (projectiveEquiv J P hP) a)) :
    HasProjectiveTransposeCoordinates J a := by
  obtain ⟨D, hD⟩ := ha
  let e := projectiveEquiv J P hP
  refine ⟨P * D, fun g => ?_⟩
  have hp : (standardForm J).specialToProjective (specialEquiv J P hP g) =
      e (J.specialToProjective g) := by
    apply Subtype.ext
    rw [(standardForm J).specialToProjective_apply_val, specialEquiv_apply,
      projectiveEquiv_apply, J.specialToProjective_apply_val]
    simp only [map_mul, map_inv]
  have h := hD (specialEquiv J P hP g)
  rw [hp] at h
  change (ProjGenLinGroup.mk D)⁻¹ *
      (e (a (e.symm (e (J.specialToProjective g))))).val * ProjGenLinGroup.mk D = _ at h
  rw [e.symm_apply_apply, projectiveEquiv_apply, specialEquiv_apply] at h
  simpa [map_mul, map_inv, mul_assoc] using h

/-- Every non-inner involution of the actual projective SU₃ image admits
natural matrix coordinates in which it is the literal inverse transpose.
The matrix witness retains both the original Hermitian basis change and the
unitary conjugator furnished by projective descent. -/
theorem hasProjectiveTransposeCoordinates_of_outer_involution [Finite F]
    (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (ho : ¬ ∃ x, a = MulAut.conj x) :
    HasProjectiveTransposeCoordinates J a := by
  let : CharP F 2 := by
    let := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (p := 2) (f := s * 2) (by
      rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s
    (by omega) hcard hconj
  obtain ⟨P, hP⟩ := exists_standard_basis J (2 ^ s) hcard hf
  let J₀ := standardForm J
  let e := projectiveEquiv J P hP
  let a₀ := MulAut.congr e a
  have ha₀ : a₀ ^ 2 = 1 := by
    change (MulAut.congr e a) ^ 2 = 1
    rw [← map_pow, ha, map_one]
  have ho₀ : ¬ ∃ x, a₀ = MulAut.conj x :=
    fun h => ho ((MulAut.congr_inner_iff e a).mp h)
  have hγ := J₀.projectiveGraphAut_isEntrywiseConjugation rfl
  obtain ⟨u, hu⟩ := J₀.outer_involution_normal_form s hs rfl hcard hf hγ a₀ ha₀ ho₀
  obtain ⟨v, hv⟩ := J₀.unitary_twist_conjugate s hs rfl hcard hf hγ u
    (by rw [← hu]; exact ha₀)
  exact coordinates_transport J P hP a (standard_coordinates J₀ rfl hγ v a₀
    (hv.trans hu.symm))

end Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.Geometry

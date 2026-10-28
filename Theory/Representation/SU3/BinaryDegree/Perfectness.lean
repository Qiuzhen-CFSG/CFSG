module

public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import BenderSuzuki.External.Huppert.II.theorem_10_13
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Perfectness of the binary special unitary group in dimension three

For a finite field of order `(2^n)^2`, with stored involution `x ↦ x^(2^n)`,
the actual special unitary matrix group is perfect when `n ≥ 2`. Its
projective image is simple by Huppert II.10.13 and has a nontrivial cube
dividing its order, so is nonabelian and perfect.

The scalar kernel lies in the special group's derived subgroup. In an
orthonormal basis, a scalar `u` in that kernel satisfies `u^3 = 1` and
`conj(u) * u = 1`. The cyclic coordinate permutation `P` and the diagonal
matrix `D = diag(1,u,u^2)` are special unitary, and `P * D = u * D * P`.
Thus their commutator is the given scalar. Huppert II.10.4(a) supplies the
orthonormal basis; conjugating these actual matrices preserves both the
isometry and determinant-one equations for the original arbitrary form.
Perfectness then lifts from the projective image because the kernel is
already contained in the derived subgroup.

This proves the concrete perfectness input for the binary degree minimum;
it is used in the quasisimple unitary case of Aschbacher--Smith A.3.6(2),
printed p.43, and the classical group setting of GLS3 §2.9. The private
basis-change calculation follows the existing `FormTransport` proof in
`Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions`.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open scoped commutatorElement
namespace Representation.SU3.BinaryDegree
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

private theorem orthonormal_conjugate_mem (J : HermitianForm 3 F) (C B : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = 1) :
    C * B * C⁻¹ ∈ J.specialSubgroup ↔
      J.conjTranspose B.val * B.val = 1 ∧ GeneralLinearGroup.det B = 1 := by
  rw [J.mem_specialSubgroup_iff, conjugate_preserves_iff, hC]
  simp only [mul_one, map_mul, map_inv, mul_assoc, mul_mul_inv_cancel'_right]

private theorem scalar_mem_commutator (J : HermitianForm 3 F) (C : GL (Fin 3) F)
    (hC : J.conjTranspose C.val * J.form * C.val = 1)
    (x : J.specialSubgroup) (u : Fˣ)
    (hu : GeneralLinearGroup.scalar (Fin 3) u = x.val) :
    x ∈ commutator J.specialSubgroup := by
  let S := GeneralLinearGroup.scalar (Fin 3) u
  have hcentral : S ∈ center (GL (Fin 3) F) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩
  have hCS : C * S * C⁻¹ = S := by
    rw [mem_center_iff.mp hcentral C, mul_inv_cancel_right]
  have hS := (orthonormal_conjugate_mem J C S hC).mp (by
    rw [hCS, show S = x.val from hu]
    exact x.property)
  have hu3 : (u : F) ^ 3 = 1 := by
    have hd := hS.2
    dsimp [S] at hd
    rw [GeneralLinearGroup.det_scalar] at hd
    have hd' := congrArg (fun z : Fˣ => (z : F)) hd
    simpa using hd'
  have hnorm : J.conj (u : F) * (u : F) = 1 := by
    have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) hS.1
    simpa [S, GeneralLinearGroup.scalar, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_succ] using he
  let Pm : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 0, 0, 1; 1, 0, 0]
  let Dm : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, (u : F), 0; 0, 0, (u : F)^2]
  have hPdet : Pm.det = 1 := by simp [Pm, Matrix.det_fin_three]
  have hDdet : Dm.det = 1 := by simpa [Dm, Matrix.det_fin_three, ← pow_succ'] using hu3
  let P := GeneralLinearGroup.mkOfDetNeZero Pm (hPdet ▸ one_ne_zero)
  let D := GeneralLinearGroup.mkOfDetNeZero Dm (hDdet ▸ one_ne_zero)
  have hPunit : J.conjTranspose P.val * P.val = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Pm, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ]
  have hDunit : J.conjTranspose D.val * D.val = 1 := by
    have hnorm2 : J.conj (u : F) ^ 2 * (u : F)^2 = 1 := by
      rw [← mul_pow, hnorm, one_pow]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, Dm, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ,
        hnorm, hnorm2]
  have hPD : P * D = S * (D * P) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, D, S, Pm, Dm, GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_succ, ← pow_succ', hu3]
    ring
  let a : J.specialSubgroup := ⟨C * P * C⁻¹, (orthonormal_conjugate_mem J C P hC).mpr
    ⟨hPunit, by apply Units.ext; simpa [P] using hPdet⟩⟩
  let b : J.specialSubgroup := ⟨C * D * C⁻¹, (orthonormal_conjugate_mem J C D hC).mpr
    ⟨hDunit, by apply Units.ext; simpa [D] using hDdet⟩⟩
  have hab : a * b = x * (b * a) := by
    apply Subtype.ext
    change (C * P * C⁻¹) * (C * D * C⁻¹) = x.val * ((C * D * C⁻¹) * (C * P * C⁻¹))
    rw [← hu]
    change _ = S * _
    calc
      _ = C * (P * D) * C⁻¹ := by group
      _ = C * (S * (D * P)) * C⁻¹ := by rw [hPD]
      _ = (C * S * C⁻¹) * ((C * D * C⁻¹) * (C * P * C⁻¹)) := by group
      _ = S * ((C * D * C⁻¹) * (C * P * C⁻¹)) := by rw [hCS]
  have hc : ⁅a, b⁆ = x := by
    rw [commutatorElement_def, hab]
    group
  rw [← hc]
  exact Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)

/-- Every scalar in the special-to-projective kernel is a commutator in an
orthonormal basis, and hence belongs to the derived subgroup for any form. -/
theorem specialToProjective_ker_le_commutator
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {q : ℕ} (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    J.specialToProjective.ker ≤ commutator J.specialSubgroup := by
  obtain ⟨C, hC⟩ :=
    BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis 3 J q hcard hfixed
  intro x hx
  have hz : x.val ∈ center (GL (Fin 3) F) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨u, hu⟩ := hz
  exact scalar_mem_commutator J C hC x u hu

open scoped IsMulCommutative in
/-- The actual projective unitary group is perfect in the binary simple range. -/
theorem isPerfect_projective {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  have hq : 2 < 2 ^ n := (by decide : 2 < 2 ^ 2).trans_le
    (Nat.pow_le_pow_right (by decide) hn)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J (2 ^ n) hq hcard hf
  rcases Subgroup.Normal.eq_bot_or_eq_top
      (inferInstance : (commutator (ProjectiveSpecialUnitaryMatrixGroup J)).Normal) with hb | ht
  · have : IsMulCommutative (ProjectiveSpecialUnitaryMatrixGroup J) :=
      (commutator_eq_bot_iff _).mp hb
    have hp : (Nat.card (ProjectiveSpecialUnitaryMatrixGroup J)).Prime :=
      IsSimpleGroup.prime_card
    have hd := HermitianForm.BinarySylowOrder.cube_dvd_card_projective J (by omega : n ≠ 0) hcard hconj
    rcases (Nat.dvd_prime hp).mp hd with h1 | he
    · have : 1 < (2 ^ n) ^ 3 := one_lt_pow₀ (by omega) (by decide)
      omega
    · exact (Nat.Prime.not_prime_pow (by decide : 2 ≤ 3) (he ▸ hp)).elim
  · exact ⟨ht⟩


/-- The actual special unitary group SU₃(2ⁿ) is perfect for `n ≥ 2`,
with no restriction on its stored nondegenerate Hermitian form. -/
theorem isPerfect_specialSubgroup
    {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    Group.IsPerfect J.specialSubgroup := by
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    isPerfect_projective J hn hcard hconj
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  have hk := specialToProjective_ker_le_commutator J hcard hf
  have hm : (commutator J.specialSubgroup).map J.specialToProjective = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr J.specialToProjective_surjective]
    exact Group.IsPerfect.commutator_eq_top
  have hc := congrArg (Subgroup.comap J.specialToProjective) hm
  rw [Subgroup.comap_map_eq, comap_top, sup_eq_left.mpr hk] at hc
  exact ⟨hc⟩

end Representation.SU3.BinaryDegree

module

public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Special and projective unitary groups over even fields

The concrete projective centralizer calculation proves PSU₃(q) centerless
for every q = 2ⁿ with n positive, after a genuine Hermitian basis change.
When n is even, a scalar in the kernel of SU₃(q) → PSU₃(q) has cube one
and is fixed by the field involution. Its unitary equation forces its square
to be one, so the canonical projective map is an isomorphism.

The coefficient field has order q², and the stored involution is x ↦ x^q.
These comparisons retain the actual special group and its natural action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the model
restriction in the proof of 13.8.20(a), printed p.954 (PDF p.971).
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenProjectiveComparison
open OddPrimeSylow.NormalizedOuter.FormTransport
variable {F : Type*} [Field F]

theorem center_eq_bot [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  have hnonfixed : ∃ t, J.conj t ≠ t := by
    by_contra! h
    have he : Nat.card {x : F // J.conj x = x} = Nat.card F :=
      Nat.card_congr (Equiv.subtypeUnivEquiv h)
    rw [hfixed, hcard] at he
    have hp : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
    nlinarith
  obtain ⟨e⟩ := exists_projectiveEquiv J (2 ^ n) hcard hfixed
  have hz := EvenTwoRank.standard_center_eq_bot (standardForm J) rfl hnonfixed
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro x hx
  apply e.injective
  have h := (Subgroup.centerCongr e ⟨x, hx⟩).property
  have he : (Subgroup.centerCongr e ⟨x, hx⟩ : ProjectiveSpecialUnitaryMatrixGroup
      (standardForm J)) = e x := rfl
  rw [he, hz, mem_bot] at h
  simpa only [map_one] using h

theorem specialToProjective_injective (J : HermitianForm 3 F)
    {n : ℕ} (hn : Even n) (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    Function.Injective J.specialToProjective := by
  apply J.specialToProjective.ker_eq_bot_iff.mp
  apply bot_unique
  intro x hx
  have hz : x.val ∈ center (GL (Fin 3) F) := by
    apply ProjGenLinGroup.mk_eq_one.mp
    simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨u, hu⟩ := hz
  have hu3 : u ^ 3 = 1 := by
    have hd := x.property.2
    change GeneralLinearGroup.det x.val = 1 at hd
    rw [← hu, GeneralLinearGroup.det_scalar] at hd
    simpa using hd
  have hc3 : (u : F) ^ 3 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hu3
  have hm : 2 ^ n % 3 = 1 := by
    rw [Nat.BinaryTorusParity.two_pow_mod_three, if_pos (Nat.even_iff.mp hn)]
  have hfix : J.conj (u : F) = u := by
    rw [hconj, pow_eq_pow_mod _ hc3, hm, pow_one]
  have hunitary := x.property.1
  change J.conjTranspose x.val.val * J.form * x.val.val = J.form at hunitary
  rw [← hu] at hunitary
  have hadj : J.conjTranspose (Matrix.scalar (Fin 3) (u : F)) =
      Matrix.scalar (Fin 3) (u : F) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [HermitianForm.conjTranspose, Matrix.scalar_apply, hfix]
    · simp [HermitianForm.conjTranspose, Matrix.scalar_apply, hij, Ne.symm hij]
  change J.conjTranspose (Matrix.scalar (Fin 3) (u : F)) * J.form *
    Matrix.scalar (Fin 3) (u : F) = J.form at hunitary
  rw [hadj] at hunitary
  obtain ⟨j, hj⟩ : ∃ j, J.form 0 j ≠ 0 := by
    by_contra! h
    exact J.form_nondegenerate (Matrix.det_eq_zero_of_row_eq_zero 0 h)
  have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 j) hunitary
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
  have hcsq : (u : F) ^ 2 = 1 := by
    apply mul_right_cancel₀ hj
    calc
      (u : F) ^ 2 * J.form 0 j = (u : F) * J.form 0 j * u := by ring
      _ = J.form 0 j := hentry
      _ = 1 * J.form 0 j := (one_mul _).symm
  have hu1 : u = 1 := Units.ext (by
    change (u : F) = 1
    simpa only [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hcsq, one_mul] using hc3)
  apply mem_bot.mpr
  apply Subtype.ext
  rw [← hu, hu1, map_one]
  rfl

noncomputable def specialProjectiveEquiv (J : HermitianForm 3 F)
    {n : ℕ} (hn : Even n) (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    J.specialSubgroup ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  MulEquiv.ofBijective J.specialToProjective
    ⟨specialToProjective_injective J hn hconj, J.specialToProjective_surjective⟩

@[simp] theorem specialProjectiveEquiv_apply (J : HermitianForm 3 F)
    {n : ℕ} (hn : Even n) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (g : J.specialSubgroup) :
    specialProjectiveEquiv J hn hconj g = J.specialToProjective g := by
  rfl

end BenderSuzuki.MatrixGroups.HermitianForm.EvenProjectiveComparison

end

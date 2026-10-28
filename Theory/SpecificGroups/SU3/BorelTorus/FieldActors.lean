module

public import Theory.SpecificGroups.SU3.BorelTorus.Basic
public import Theory.FieldTheory.BinaryTorusInvolution.ThreeKernel
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Field
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Two-power field actors on the full unitary torus

A nonidentity field automorphism of two-power order has an involution power.
The finite field's cyclic automorphism group identifies that power with the
stored Hermitian involution. The three-kernel calculation then forces the
fixed-field degree to be three when the actor fixes the three-residual in
the full special or projective torus. The Hermitian involution does fix that
residual in degree three, so the exceptional parameter is exact.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954. The matrix-field
order is `(2^n)^2`; `n` is the degree of the fixed field. Identification of
an arbitrary group automorphism's action on the Borel quotient is separate.
-/

public section

open BenderSuzuki.External Subgroup FiniteField.BinaryTorusInvolution
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

private theorem exists_involution_power {G : Type*} [Group G] (a : G)
    {r : ℕ} (hr : a ^ (2 ^ r) = 1) (ha : a ≠ 1) :
    ∃ k : ℕ, (a ^ k) ^ 2 = 1 ∧ a ^ k ≠ 1 := by
  induction r with
  | zero => simp only [pow_zero, pow_one] at hr; exact (ha hr).elim
  | succ r ih =>
    by_cases h : a ^ (2 ^ r) = 1
    · exact ih h
    · refine ⟨2 ^ r, ?_, h⟩
      rw [← pow_mul, ← pow_succ]
      exact hr

theorem field_eq_one_or_degree_three {T : Type*} [Group T]
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (σ : E ≃+* E) {r : ℕ} (hσ : σ ^ (2 ^ r) = 1)
    (f : Eˣ →* T) (hker : IsPGroup 3 f.ker)
    (hfix : ∀ u ∈ pResidual 3 Eˣ, f (Units.map σ.toMonoidHom u) = f u) :
    σ = 1 ∨ n = 3 := by
  by_cases he : σ = 1
  · exact Or.inl he
  obtain ⟨k, hk, hkne⟩ := exists_involution_power σ hσ he
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  have hpow : σ ^ k = J.conj :=
    field_involution_eq_conj J n (by omega) hcard hfixed (σ ^ k) hk hkne
  have hfixpow := fixed_residual_mod_kernel_pow σ f hfix k
  rw [hpow] at hfixpow
  apply Or.inr
  apply degree_three_of_fixed_residual_mod_kernel J.conj hn _ hconj f hker hfixpow
  rw [hcard, ← pow_mul, Nat.mul_comm n 2]

theorem special_field_eq_one_or_degree_three
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (σ : E ≃+* E) {r : ℕ} (hσ : σ ^ (2 ^ r) = 1)
    (hfix : ∀ u ∈ pResidual 3 Eˣ,
      hermitianTorusSU J hJ (Units.map σ.toMonoidHom u) = hermitianTorusSU J hJ u) :
    σ = 1 ∨ n = 3 :=
  field_eq_one_or_degree_three J hn hcard hconj σ hσ (hermitianTorusSU J hJ)
    (IsPGroup.ker_isPGroup_of_injective (special_injective J hJ)) hfix

theorem projective_field_eq_one_or_degree_three
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n))
    (σ : E ≃+* E) {r : ℕ} (hσ : σ ^ (2 ^ r) = 1)
    (hfix : ∀ u ∈ pResidual 3 Eˣ,
      hermitianTorusPSU J hJ (Units.map σ.toMonoidHom u) = hermitianTorusPSU J hJ u) :
    σ = 1 ∨ n = 3 :=
  field_eq_one_or_degree_three J hn hcard hconj σ hσ (hermitianTorusPSU J hJ)
    (projective_ker_isThreeGroup J hJ) hfix

theorem special_involution_fixes_iff
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) :
    (∀ u ∈ pResidual 3 Eˣ,
      hermitianTorusSU J hJ (Units.map J.conj.toMonoidHom u) = hermitianTorusSU J hJ u) ↔
      n = 3 := by
  apply fixed_residual_mod_kernel_iff_degree_three J.conj hn _ hconj
    (hermitianTorusSU J hJ) (IsPGroup.ker_isPGroup_of_injective (special_injective J hJ))
  rw [hcard, ← pow_mul, Nat.mul_comm n 2]

theorem projective_involution_fixes_iff
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) :
    (∀ u ∈ pResidual 3 Eˣ,
      hermitianTorusPSU J hJ (Units.map J.conj.toMonoidHom u) = hermitianTorusPSU J hJ u) ↔
      n = 3 := by
  apply fixed_residual_mod_kernel_iff_degree_three J.conj hn _ hconj
    (hermitianTorusPSU J hJ) (projective_ker_isThreeGroup J hJ)
  rw [hcard, ← pow_mul, Nat.mul_comm n 2]

end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus

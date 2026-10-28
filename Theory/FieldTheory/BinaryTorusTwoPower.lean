module

public import Theory.FieldTheory.BinaryTorusInvolution
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Two-power field automorphisms fixing a binary residual torus

An actual field involution is the half-degree Frobenius: express it as a
power of the prime-field Frobenius and use its exact order. If an arbitrary
coefficient automorphism has two-power order and fixes O³(Fˣ), a nontrivial
last power would be such an involution. The multiplicative displacement
calculation then forces field degree two or six. Induction on the supplied
two-power order bound proves triviality in every other degree.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954. The matrix actor
itself is never assumed involutory. Identifying its coefficient factor and
proving that factor has two-power order are separate matrix-group obligations.
-/

public section

open Subgroup
namespace FiniteField.BinaryTorusTwoPower
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

private noncomputable def primeAut (σ : F ≃+* F) : F ≃ₐ[ZMod 2] F :=
  AlgEquiv.ofRingEquiv (f := σ) (by
    intro x
    have h : σ.toRingHom.comp (algebraMap (ZMod 2) F) = algebraMap (ZMod 2) F :=
      RingHom.ext_zmod _ _
    exact DFunLike.congr_fun h x)

omit [Finite F] in
private theorem primeAut_apply (σ : F ≃+* F) (x : F) : primeAut σ x = σ x := by
  unfold primeAut
  exact AlgEquiv.ofRingEquiv_apply _ _

private theorem prime_finrank {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Module.finrank (ZMod 2) F = n := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
  simpa only [Nat.card_eq_fintype_card, ZMod.card] using h.symm.trans hF

/-- An actual nonidentity involution is the half-degree Frobenius. -/
theorem involution_eq_half_frobenius {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (σ : F ≃+* F) (hσ : σ ^ 2 = 1) (hne : σ ≠ 1) :
    ∃ m, 0 < m ∧ n = 2 * m ∧ ∀ x : F, σ x = x ^ (2 ^ m) := by
  let φ := frobeniusAlgEquivOfAlgebraic (ZMod 2) F
  obtain ⟨⟨m,hm⟩,he⟩ :=
    (bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) F).surjective (primeAut σ)
  have he' : φ ^ m = primeAut σ := he
  have hm0 : m ≠ 0 := by
    intro hz
    apply hne
    ext x
    change σ x = x
    have h := DFunLike.congr_fun he' x
    simpa only [hz, pow_zero, AlgEquiv.one_apply, primeAut_apply] using h.symm
  have hs : (primeAut σ) ^ 2 = 1 := by
    ext x
    exact DFunLike.congr_fun hσ x
  have hd : n ∣ m * 2 := by
    rw [← prime_finrank hF, ← orderOf_frobeniusAlgEquivOfAlgebraic (ZMod 2) F]
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, he', hs]
  have hm' : m < n := by simpa only [prime_finrank hF] using hm
  have hn : n = 2 * m := by
    obtain ⟨j,hj⟩ := hd
    have hj0 : j ≠ 0 := by intro h; simp [h] at hj; omega
    have hj2 : j < 2 := by nlinarith
    have : j = 1 := by omega
    simp only [this, mul_one] at hj
    omega
  refine ⟨m, by omega, hn, fun x => ?_⟩
  have h := DFunLike.congr_fun he' x
  rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate] at h
  simpa only [ZMod.card, primeAut_apply] using h.symm

omit [Finite F] [CharP F 2] in
private theorem fixed_pow (σ : F ≃+* F)
    (hfix : ∀ u ∈ pResidual 3 Fˣ, Units.map σ.toMonoidHom u = u) (j : ℕ) :
    ∀ u ∈ pResidual 3 Fˣ, Units.map (σ ^ j).toMonoidHom u = u := by
  intro u hu
  apply Units.ext
  induction j with
  | zero => rfl
  | succ j ih =>
    change (σ ^ (j + 1)) (u : F) = (u : F)
    rw [pow_succ]
    change (σ ^ j) (σ (u : F)) = (u : F)
    rw [show σ (u : F) = (u : F) from congrArg Units.val (hfix u hu)]
    exact ih

/-- An arbitrary two-power coefficient automorphism fixing the three-residual
is trivial outside the two exceptional degrees. -/
theorem eq_one_of_fixed_residual {n k : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn2 : n ≠ 2) (hn6 : n ≠ 6) (σ : F ≃+* F)
    (hσ : σ ^ (2 ^ k) = 1)
    (hfix : ∀ u ∈ pResidual 3 Fˣ, Units.map σ.toMonoidHom u = u) : σ = 1 := by
  induction k with
  | zero => simpa using hσ
  | succ k ih =>
    by_cases he : σ ^ (2 ^ k) = 1
    · exact ih he
    · let τ := σ ^ (2 ^ k)
      have ht : τ ^ 2 = 1 := by simpa only [τ, ← pow_mul, ← pow_succ] using hσ
      obtain ⟨m,hm,hn,hτ⟩ := involution_eq_half_frobenius hF τ ht he
      have hFm : Nat.card F = 2 ^ (2 * m) := by rw [← hn]; exact hF
      have hm' := BinaryTorusInvolution.half_degree_of_fixed_residual τ hm hFm hτ
        (fixed_pow σ hfix (2 ^ k))
      rcases hm' with hm' | hm' <;> omega

end FiniteField.BinaryTorusTwoPower

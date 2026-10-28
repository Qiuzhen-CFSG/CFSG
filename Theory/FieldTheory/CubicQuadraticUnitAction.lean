module

public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Quadratic field action modulo a cubic torus kernel

For a field of order `2^(2*n)`, with `n ≥ 2`, an automorphism whose double
multiplicative displacement always has cube one is the identity. Express the
automorphism as the `k`-th binary Frobenius and test a generator of the units:
`2^(2*n)-1` divides `3*(2^k-1)^2`. Taking a gcd replaces `k` by
`d = gcd (2*n) k`. If `(2*n)/d ≥ 3`, comparison with the cube of `2^d` is
impossible. If that quotient is two, cancellation forces `2^d+1` to divide
six; its parity then leaves only the excluded field of order four.

This supplies the cubic-kernel field calculation for projective unitary
Cartan subgroups in Aschbacher–Smith, F.1.3(5), printed p.260. It requires
no order or coprimality hypothesis on the automorphism. The literal projective
torus application is in `Theory.SpecificGroups.SU3.BorelTorus.QuadraticField`.
-/

public section
namespace RingEquiv

private theorem gcd_square_reduction {N A c : ℕ} (h : N ∣ c * A ^ 2) :
    N ∣ c * Nat.gcd N A ^ 2 := by
  have h₁ : N ∣ (c * A) * Nat.gcd N A :=
    Nat.dvd_mul_gcd_iff_dvd_mul.mpr (by simpa [pow_two, mul_assoc] using h)
  have h₂ : N ∣ Nat.gcd N A * (c * Nat.gcd N A) :=
    Nat.dvd_gcd_mul_iff_dvd_mul.mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using h₁)
  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h₂

private theorem binary_cubic_bound {m d : ℕ} (hm : 4 ≤ m) (hd : 0 < d)
    (hdm : d ∣ m) (hlt : d < m) : ¬ (2 ^ m - 1 ∣ 3 * (2 ^ d - 1) ^ 2) := by
  intro h
  have hq : 2 ≤ 2 ^ d := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hd
  have hsub : 0 < 2 ^ d - 1 := by omega
  have hp : 0 < 3 * (2 ^ d - 1) ^ 2 := by positivity
  have hle := Nat.le_of_dvd hp h
  obtain ⟨r, hr⟩ := hdm
  have hr2 : 2 ≤ r := by
    by_contra hn
    have : r = 0 ∨ r = 1 := by omega
    rcases this with rfl | rfl <;> simp_all
  by_cases hr3 : 3 ≤ r
  · have h3d : d * 3 ≤ m := by rw [hr]; exact Nat.mul_le_mul_left d hr3
    have hpow := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) h3d
    rw [pow_mul] at hpow
    have he : 2 ^ d = (2 ^ d - 1) + 1 := by omega
    rw [he] at hpow
    have hmpos : 0 < 2 ^ m := by positivity
    have hc : (2 ^ d - 1 + 1) ^ 3 ≤ 3 * (2 ^ d - 1) ^ 2 + 1 := by omega
    nlinarith only [hc, hsub, Nat.zero_le ((2 ^ d - 1) ^ 3)]
  · have hr' : r = 2 := by omega
    have hm' : m = d * 2 := by simpa [hr'] using hr
    have hd2 : 2 ≤ d := by omega
    have hq4 : 4 ≤ 2 ^ d := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hd2
    have hfac : 2 ^ m - 1 = (2 ^ d - 1) * (2 ^ d + 1) := by
      rw [hm', pow_mul]
      simpa [mul_comm] using Nat.sq_sub_sq (2 ^ d) 1
    rw [hfac] at h
    have hc : 2 ^ d + 1 ∣ 3 * (2 ^ d - 1) := by
      apply (Nat.mul_dvd_mul_iff_left (show 0 < 2 ^ d - 1 by omega)).mp
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h
    have h6 : 2 ^ d + 1 ∣ 6 := by
      have he : 3 * (2 ^ d + 1) - 3 * (2 ^ d - 1) = 6 := by omega
      simpa only [he] using Nat.dvd_sub (dvd_mul_left (2 ^ d + 1) 3) hc
    have hq6 := Nat.le_of_dvd (by decide : 0 < 6) h6
    have heven : 2 ∣ 2 ^ d := dvd_pow_self 2 (by omega : d ≠ 0)
    have he : 2 ^ d = 4 := by omega
    norm_num [he] at h6

private theorem binary_cubic_exponent_eq_zero {m k : ℕ} (hm : 4 ≤ m) (hk : k < m)
    (h : 2 ^ m - 1 ∣ 3 * (2 ^ k - 1) ^ 2) : k = 0 := by
  by_contra hk0
  have hg : 0 < Nat.gcd m k := Nat.gcd_pos_of_pos_left k (by omega)
  have hgl : Nat.gcd m k < m := lt_of_le_of_lt (Nat.gcd_le_right m (by omega)) hk
  have hred := gcd_square_reduction h
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hred
  exact binary_cubic_bound hm hg (Nat.gcd_dvd_left m k) hgl hred

private theorem binary_frobenius_exponent {E : Type*} [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hcard : Nat.card E = 2 ^ m) (σ : E ≃+* E) :
    ∃ k : ℕ, k < m ∧ ∀ x : E, σ x = x ^ (2 ^ k) := by
  let : Fintype E := Fintype.ofFinite E
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  let σ' : E ≃ₐ[ZMod 2] E := AlgEquiv.ofRingEquiv (f := σ) (by
    intro x
    have h : σ.toRingHom.comp (algebraMap (ZMod 2) E) = algebraMap (ZMod 2) E :=
      RingHom.ext_zmod _ _
    exact DFunLike.congr_fun h x)
  have hd : Module.finrank (ZMod 2) E = m := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E)
    rw [hcard, Nat.card_eq_fintype_card, ZMod.card] at hc
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ))) hc.symm
  obtain ⟨k, hk⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
    (ZMod 2) E).surjective σ'
  refine ⟨k, hd ▸ k.isLt, ?_⟩
  intro x
  have hx := DFunLike.congr_fun hk x
  change (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) E ^ (k : ℕ)) x = σ x at hx
  simpa only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    pow_iterate, ZMod.card] using hx.symm

/-- A binary field automorphism with cubic double multiplicative displacement is
trivial when the field has square order at least sixteen. The lower bound on `n`
is necessary: the nontrivial automorphism of GF(4) satisfies the displacement condition. -/
theorem eq_one_of_cubic_quadratic_units {E : Type*} [Field E] [Finite E] {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2) (σ : E ≃+* E)
    (h : ∀ k : Eˣ, (Units.map σ.toMonoidHom
      (Units.map σ.toMonoidHom k * k⁻¹) *
        (Units.map σ.toMonoidHom k * k⁻¹)⁻¹) ^ 3 = 1) : σ = 1 := by
  let : Fintype E := Fintype.ofFinite E
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard' : Nat.card E = 2 ^ (n * 2) := by simpa only [pow_mul] using hcard
  let : CharP E 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard')
  obtain ⟨k, hk, hσ⟩ := binary_frobenius_exponent hcard' σ
  have hu (u : Eˣ) : Units.map σ.toMonoidHom u * u⁻¹ = u ^ (2 ^ k - 1) := by
    have he : Units.map σ.toMonoidHom u = u ^ (2 ^ k) := Units.ext (hσ u)
    rw [he, pow_sub _ (Nat.one_le_pow _ _ (by decide : 1 ≤ (2 : ℕ))), pow_one]
  obtain ⟨u, huorder⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Eˣ)
  have he := h u
  rw [hu, hu, ← pow_mul, ← pow_mul] at he
  have hdiv : 2 ^ (n * 2) - 1 ∣ 3 * (2 ^ k - 1) ^ 2 := by
    have := orderOf_dvd_of_pow_eq_one he
    rw [huorder, Nat.card_units, hcard'] at this
    simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
  have hk0 := binary_cubic_exponent_eq_zero (by omega : 4 ≤ n * 2) hk hdiv
  ext x
  change σ x = x
  simpa only [hk0, pow_zero, pow_one] using hσ x

end RingEquiv

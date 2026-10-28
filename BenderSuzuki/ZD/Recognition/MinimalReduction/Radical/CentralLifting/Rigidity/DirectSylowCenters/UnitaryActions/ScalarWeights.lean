module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.DirectSylowCenters.UnitaryActions.Coordinates
public import Mathlib.Data.Nat.GCD.Basic

/-!
# Primitive scalars of the actual binary unitary torus

For a fixed field of order q = 2ⁿ, n ≥ 2, the same primitive unit k gives
first-coordinate weight λ = k/conj(k)² of order (q² - 1)/gcd(q + 1, 3)
and central scalar ν = inverseNorm(k) of order q - 1. Huppert II.10.4
identifies conjugation with q-power Frobenius; norm surjectivity gives the
central scalar order.

The weight order exceeds q + 1, including q = 4, where the gcd is one.
Any smaller binary Frobenius period would give a proper divisor of 2n,
at most n, contradicting this order bound. An inverse Frobenius conjugate
would have exponent index divisible by n, and is excluded by the same bound.
Frobenius injectivity then excludes reciprocal pairs of conjugate weights.

The final theorem applies this calculation to the literal torusNormalizer
and projective root center, discharging the fixed-center premise used by
root_action_of_field_pairings in the separately owned assembly module.

Source: the torus coordinates of Huppert II.10.4 and II.10.12, as used in
the direct Sylow-center argument for GLS4, Chapter 4, Lemma 2.8(c).
-/

public section

namespace BenderSuzuki.ZD.DirectSylowCenters.UnitaryActions


private theorem square_sub_one (q : ℕ) (hq : 1 ≤ q) :
    q ^ 2 - 1 = (q - 1) * (q + 1) := by
  have := Nat.sub_add_cancel hq
  have hs : 1 ≤ q ^ 2 := by nlinarith
  have := Nat.sub_add_cancel hs
  nlinarith

private theorem weight_exponent_gcd (q : ℕ) (hq : 1 ≤ q) :
    Nat.gcd (q ^ 2 - 1) (2 * q - 1) = Nat.gcd (q + 1) 3 := by
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  have he : (2 * q + 1)*(2 * q - 1) = 4*(q ^ 2-1)+3 := by
    have := Nat.sub_add_cancel (by omega : 1 ≤ 2 * q)
    have := Nat.sub_add_cancel hq2
    nlinarith
  have h3 : Nat.gcd (q ^ 2-1) (2 * q - 1) ∣ 3 := by
    have hh := Nat.dvd_sub (dvd_mul_of_dvd_right (Nat.gcd_dvd_right (q ^ 2-1) (2 * q - 1)) (2 * q + 1))
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_left (q ^ 2-1) (2 * q - 1)) 4)
    rwa [he, Nat.add_sub_cancel_left] at hh
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd _ h3
    rcases (by decide : Nat.Prime 3).eq_one_or_self_of_dvd _ h3 with hg | hg
    · simp [hg]
    · have hh := Nat.gcd_dvd_right (q ^ 2-1) (2 * q - 1)
      rw [hg] at hh ⊢
      omega
  · apply Nat.dvd_gcd
    · exact (Nat.gcd_dvd_left (q + 1) 3).trans ⟨q - 1, by rw [square_sub_one q hq]; nlinarith⟩
    · have h := Nat.gcd_dvd_left (q + 1) 3
      have h' := Nat.gcd_dvd_right (q + 1) 3
      have hh := Nat.dvd_sub (dvd_mul_of_dvd_right h 2) h'
      convert hh using 1
      omega

/-- The scalar-order bound, retaining the genuine gcd in the case q = 4. -/
theorem unitary_scalar_order_gt (q : ℕ) (hq : 4 ≤ q) :
    q + 1 < (q ^ 2 - 1) / Nat.gcd (q + 1) 3 := by
  by_cases h4 : q = 4
  · subst q; norm_num
  have hd := Nat.gcd_dvd_right (q + 1) 3
  have hdpos : 0 < Nat.gcd (q + 1) 3 := Nat.gcd_pos_of_pos_right _ (by decide)
  have hdle : Nat.gcd (q + 1) 3 ≤ 3 := Nat.le_of_dvd (by decide) hd
  have hm := Nat.div_add_mod (q ^ 2-1) (Nat.gcd (q + 1) 3)
  have hzero : (q ^ 2-1) % Nat.gcd (q + 1) 3 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact (Nat.gcd_dvd_left (q + 1) 3).trans ⟨q - 1, by rw [square_sub_one q (by omega)]; nlinarith⟩
  rw [hzero, Nat.add_zero] at hm
  have hsq : 1 ≤ q ^ 2 := by nlinarith
  have hsub := Nat.sub_add_cancel hsq
  by_contra hc
  have hmul : (q ^ 2-1) / Nat.gcd (q + 1) 3 * Nat.gcd (q + 1) 3 ≤ (q + 1)*3 :=
    Nat.mul_le_mul (by omega) hdle
  have hq5 : 5 ≤ q := by omega
  nlinarith


private theorem half_bound {d n : ℕ} (hn : 0 < n) (hd : d ∣ 2 * n) (hne : d ≠ 2 * n) : d ≤ n := by
  obtain ⟨c, hc⟩ := hd
  have hc2 : 2 ≤ c := by
    by_contra h
    have : c = 0 ∨ c = 1 := by omega
    rcases this with rfl | rfl <;> simp_all
  nlinarith

private theorem period_dvd_of_large_order {G : Type*} [Group G] (g : G) {n : ℕ} (hn : 0 < n)
    (horder : 2 ^ n+1 < orderOf g) (hfull : g ^ (2^(2 * n)-1) = 1)
    {i : ℕ} (hi : g^(2 ^ i) = g) : 2 * n ∣ i := by
  have hd : orderOf g ∣ 2 ^ i-1 := by
    apply orderOf_dvd_of_pow_eq_one
    apply mul_right_cancel (b := g)
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow i 2 (by decide)), hi, one_mul]
  have hdf := orderOf_dvd_of_pow_eq_one hfull
  have hg := Nat.dvd_gcd hd hdf
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hg
  by_contra hni
  have hne : Nat.gcd i (2 * n) ≠ 2 * n := by
    intro h
    have := Nat.gcd_dvd_left i (2 * n)
    exact hni (h ▸ this)
  have hhalf := half_bound hn (Nat.gcd_dvd_right i (2 * n)) hne
  have hpos : 0 < Nat.gcd i (2 * n) := Nat.gcd_pos_of_pos_right _ (by omega)
  have hpowpos : 0 < 2 ^ Nat.gcd i (2 * n) - 1 := by
    have := Nat.one_lt_pow hpos.ne' (by decide : 1 < 2)
    omega
  have hle := Nat.le_of_dvd hpowpos hg
  have hpowle : 2 ^ Nat.gcd i (2 * n) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hhalf
  omega

private theorem inverse_not_power {G : Type*} [Group G] (g : G) {n : ℕ}
    (horder : 2 ^ n+1 < orderOf g)
    (period : ∀ i : ℕ, g^(2 ^ i) = g → 2 * n ∣ i)
    {i : ℕ} (hi : i < 2 * n) : g^(2 ^ i) ≠ g⁻¹ := by
  intro he
  have htwice : g^(2^(2 * i)) = g := by
    calc
      g^(2^(2 * i)) = (g^(2 ^ i))^(2 ^ i) := by rw [← pow_mul, ← pow_add]; congr 2; omega
      _ = (g⁻¹)^(2 ^ i) := by rw [he]
      _ = (g^(2 ^ i))⁻¹ := by rw [inv_pow]
      _ = g := by rw [he, inv_inv]
  have hdiv : n ∣ i := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) (period _ htwice)
  have hibound : i ≤ n := by
    obtain ⟨c, rfl⟩ := hdiv
    have hc : c ≤ 1 := by nlinarith
    nlinarith
  have ho : orderOf g ∣ 2 ^ i+1 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_succ, he, inv_mul_cancel]
  have hol := Nat.le_of_dvd (by positivity : 0 < 2 ^ i+1) ho
  have hip := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hibound
  omega

private theorem separated_of_inverse_not_power {K : Type*} [Field K] [CharP K 2]
    (g : Kˣ) {n : ℕ}
    (hinv : ∀ i : Fin (2 * n), (g : K)^(2^(i : ℕ)) ≠ (g : K)⁻¹)
    (i j : Fin (2 * n)) : (g : K)^(2^(i : ℕ)) * (g : K)^(2^(j : ℕ)) ≠ 1 := by
  have aux (a b : Fin (2 * n)) (hab : (a : ℕ) ≤ b) :
      (g : K)^(2^(a : ℕ)) * (g : K)^(2^(b : ℕ)) ≠ 1 := by
    intro he
    have hd : (b : ℕ) - a < 2 * n := (Nat.sub_le _ _).trans_lt b.isLt
    apply hinv ⟨(b : ℕ)-a, hd⟩
    have hh : (g : K) * (g : K)^(2^((b : ℕ)-a)) = 1 := by
      apply (iterateFrobenius K 2 (a : ℕ)).injective
      change ((g : K) * (g : K)^(2^((b : ℕ)-a)))^(2^(a : ℕ)) = 1^(2^(a : ℕ))
      rw [mul_pow, one_pow, ← pow_mul, ← Nat.pow_add, Nat.sub_add_cancel hab]
      exact he
    change (g : K)^(2^((b : ℕ)-a)) = (g : K)⁻¹
    calc
      _ = (g : K)⁻¹ * ((g : K) * (g : K)^(2^((b : ℕ)-a))) :=
        (inv_mul_cancel_left₀ g.ne_zero _).symm
      _ = (g : K)⁻¹ := by rw [hh, mul_one]
  rcases le_total (i : ℕ) (j : ℕ) with hij | hji
  · exact aux i j hij
  · simpa only [mul_comm] using aux j i hji

open Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.BorelTorus HermitianForm.BorelTorus.EvenCenterAction
open HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
variable {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K)
section ArbitraryQ
variable {q : ℕ} (hq : 1 ≤ q) (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)

include hcard hfixed in
/-- The central scalar for this primitive unit generates the fixed-field units. -/
theorem primitive_inverseNorm_order (k : Kˣ) (hk : orderOf k = Nat.card K - 1) :
    orderOf (inverseNorm J k) = q - 1 := by
  have htop : zpowers k = ⊤ := (zpowers k).eq_top_of_card_eq (by
    rw [Nat.card_zpowers, hk, Nat.card_units])
  have hgen : ∀ u, u ∈ zpowers (inverseNorm J k) := by
    intro u
    obtain ⟨v, rfl⟩ := inverseNorm_surjective J hcard hfixed u
    have hv : v ∈ zpowers k := by rw [htop]; trivial
    obtain ⟨i, rfl⟩ := hv
    exact ⟨i, (map_zpow _ _ _).symm⟩
  rw [orderOf_eq_card_of_forall_mem_zpowers hgen, Nat.card_units]
  exact congrArg (fun t : ℕ => t - 1) hfixed

include hq hcard hfixed in
private theorem weight_inverse_eq_power (k : Kˣ) : (torusWeight J k)⁻¹ = k^(2 * q - 1) := by
  have hconj : Units.map J.conj.toMonoidHom k = k^q := by
    apply Units.ext
    exact huppert_II_10_4_conj_eq_frobenius J q hcard hfixed k
  rw [torusWeight, MonoidHom.coe_mk, OneHom.coe_mk, hconj]
  simp only [mul_inv_rev, inv_pow, inv_inv]
  rw [← pow_mul, Nat.mul_comm q 2, pow_sub k (by omega : 1 ≤ 2 * q), pow_one]


include hq hcard hfixed in
/-- The first-coordinate weight of the specified primitive unit has the full
projective torus order. -/
theorem primitive_weight_order (k : Kˣ) (hk : orderOf k = Nat.card K - 1) :
    orderOf (torusWeight J k) = (q ^ 2 - 1) / Nat.gcd (q + 1) 3 := by
  rw [← orderOf_inv (torusWeight J k), weight_inverse_eq_power J hq hcard hfixed,
    orderOf_pow, hk, hcard, weight_exponent_gcd q hq]

end ArbitraryQ

private theorem binary_q_ge_four {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n := by
  simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn

variable {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card K = (2 ^ n)^2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ n)

include hn hcard hfixed in
/-- The central scalar of every primitive unit is nonidentity. -/
theorem primitive_inverseNorm_ne_one (k : Kˣ) (hk : orderOf k = Nat.card K - 1) :
    inverseNorm J k ≠ 1 := by
  intro he
  have ho := primitive_inverseNorm_order J hcard hfixed k hk
  rw [he, orderOf_one] at ho
  have := binary_q_ge_four hn
  omega

include hn hcard hfixed in
/-- The literal first-coordinate scalar has order greater than q + 1. -/
theorem primitive_weight_order_gt (k : Kˣ) (hk : orderOf k = Nat.card K - 1) :
    2 ^ n+1 < orderOf (torusWeight J k) := by
  rw [primitive_weight_order J (by have := binary_q_ge_four hn; omega) hcard hfixed k hk]
  exact unitary_scalar_order_gt _ (binary_q_ge_four hn)

omit [Finite K] in
include hcard in
private theorem weight_full_power (k : Kˣ) :
    (torusWeight J k)^(2^(2 * n)-1) = 1 := by
  have he := pow_card_eq_one' (x := torusWeight J k)
  rw [Nat.card_units, hcard] at he
  simpa only [← pow_mul, Nat.mul_comm n 2] using he

include hn hcard hfixed in
/-- Every binary Frobenius period of the literal weight is divisible by 2n. -/
theorem primitive_weight_period_dvd (k : Kˣ) (hk : orderOf k = Nat.card K - 1)
    {i : ℕ} (hi : (torusWeight J k : K)^(2 ^ i) = (torusWeight J k : K)) :
    2 * n ∣ i := by
  apply period_dvd_of_large_order (torusWeight J k) (by omega : 0 < n)
    (primitive_weight_order_gt J hn hcard hfixed k hk) (weight_full_power J hcard k)
  apply Units.ext
  exact hi

include hn hcard hfixed in
/-- The literal weight has exact binary Frobenius degree 2n. -/
theorem primitive_weight_binary_degree (k : Kˣ) (hk : orderOf k = Nat.card K - 1) :
    (torusWeight J k : K)^(2^(2 * n)) = (torusWeight J k : K) ∧
      ∀ i : ℕ, 0 < i → i < 2 * n →
        (torusWeight J k : K)^(2 ^ i) ≠ (torusWeight J k : K) := by
  constructor
  · let : Fintype K := Fintype.ofFinite K
    have he := FiniteField.pow_card (torusWeight J k : K)
    rw [← Nat.card_eq_fintype_card, hcard] at he
    simpa only [← pow_mul, Nat.mul_comm n 2] using he
  · intro i hi hil he
    have hd := primitive_weight_period_dvd J hn hcard hfixed k hk he
    have := Nat.le_of_dvd hi hd
    omega

include hn hcard hfixed in
/-- None of the 2n Frobenius conjugates is the inverse weight. -/
theorem primitive_weight_inverse_not_frobenius (k : Kˣ)
    (hk : orderOf k = Nat.card K - 1) (i : Fin (2 * n)) :
    (torusWeight J k : K)^(2^(i : ℕ)) ≠ (torusWeight J k : K)⁻¹ := by
  intro he
  apply inverse_not_power (torusWeight J k)
    (primitive_weight_order_gt J hn hcard hfixed k hk)
    (fun j hj => period_dvd_of_large_order (torusWeight J k) (by omega : 0 < n)
      (primitive_weight_order_gt J hn hcard hfixed k hk) (weight_full_power J hcard k) hj)
    i.isLt
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val] using he

include hn hcard hfixed in
/-- The reciprocal-weight separation consumed by the binary pairing argument. -/
theorem primitive_weight_separated (k : Kˣ) (hk : orderOf k = Nat.card K - 1)
    (i j : Fin (2 * n)) :
    (torusWeight J k : K)^(2^(i : ℕ)) * (torusWeight J k : K)^(2^(j : ℕ)) ≠ 1 := by
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  exact separated_of_inverse_not_power (torusWeight J k)
    (primitive_weight_inverse_not_frobenius J hn hcard hfixed k hk) i j

include hn hcard hfixed in
/-- The fixed-center premise for the actual projective torus normalizer element,
with the primitive scalar premise discharged. -/
theorem primitive_torus_center_fixed (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (k : Kˣ) (hk : orderOf k = Nat.card K - 1)
    (z : projectiveRoot J hJ) (hz : z ∈ center (projectiveRoot J hJ))
    (hfix : (projectiveRoot J hJ).normalizerMonoidHom (torusNormalizer J hJ k) z = z) :
    z = 1 := by
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  exact center_fixed J hJ hn hcard hfixed k
    (primitive_inverseNorm_ne_one J hn hcard hfixed k hk) z hz hfix

end BenderSuzuki.ZD.DirectSylowCenters.UnitaryActions

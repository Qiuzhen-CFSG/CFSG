module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Primitive binary primes at four times an odd exponent

For odd `n ≥ 3`, there is a prime modulo which `2` has order `4*n`.
This is the special case of Zsigmondy's theorem needed for binary Suzuki
representation degrees. The source is GLS2, Chapter A, Theorem 1.1
(`refs/KGroup/GLS2/ChapterA.tex`, lines 192–194).

We prove the result directly using `Φ_m(4)`, with `m = 2*n`. In characteristic
`p`, a root of `Φ_m` has order equal to the part of `m` prime to `p`. Consequently
a prime dividing both `Φ_m(4)` and `m` is the largest prime divisor of `m`.
The odd-prime geometric-sum multiplicity formula shows that its square does
not divide `Φ_m(4)`. If all prime divisors were nonprimitive, `Φ_m(4)` would
therefore be at most this single prime `p`. This contradicts
`p ≤ 3^(p-1) ≤ 3^φ(m) < Φ_m(4)`.

Finally, since `m` is even, order `m` for the square of `2` gives order `2*m`
for `2`. The argument actually works for every positive `n`; the exported
statement retains the odd-exponent hypotheses of its intended consumer.
-/

public section

open Polynomial

namespace Theory.NumberTheory

private theorem root_of_dvd {m p : ℕ}
    (hd : p ∣ ((cyclotomic m ℤ).eval 4).natAbs) :
    (cyclotomic m (ZMod p)).IsRoot 4 := by
  rw [IsRoot.def, ← map_cyclotomic_int m (ZMod p)]
  rw [eval_map, eval₂_at_ofNat]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
    (Int.natCast_dvd.mpr hd)

private theorem root_order_decomposition {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hd : p ∣ ((cyclotomic m ℤ).eval 4).natAbs) :
    ∃ k : ℕ, m = p ^ k * orderOf (4 : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, d, hpd, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.ne_one
  let : NeZero (d : ZMod p) := NeZero.of_not_dvd (ZMod p) hpd
  have hr := root_of_dvd hd
  rw [he] at hr
  have ho := (isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp hr).eq_orderOf
  exact ⟨k, by simpa only [← ho] using he⟩

private theorem root_nonzero {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hd : p ∣ ((cyclotomic m ℤ).eval 4).natAbs) : (4 : ZMod p) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hcop := coprime_of_root_cyclotomic (a := 4) hm (root_of_dvd hd)
  exact mt (ZMod.natCast_eq_zero_iff 4 p).mp (hp.coprime_iff_not_dvd.mp hcop.symm)

private theorem prime_le_of_root {m p q : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hd : p ∣ ((cyclotomic m ℤ).eval 4).natAbs) (hq : q.Prime) (hqm : q ∣ m) :
    q ≤ p := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, he⟩ := root_order_decomposition hm hp hd
  rw [he] at hqm
  rcases hq.dvd_mul.mp hqm with hqk | hqo
  · exact Nat.le_of_dvd hp.pos (hq.dvd_of_dvd_pow hqk)
  · have ho := ZMod.orderOf_dvd_card_sub_one (root_nonzero hm hp hd)
    exact (Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) (hqo.trans ho)).trans (Nat.sub_le _ _)

private theorem prime_sq_not_dvd {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hd : p ∣ ((cyclotomic m ℤ).eval 4).natAbs) (hpm : p ∣ m) :
    ¬p ^ 2 ∣ ((cyclotomic m ℤ).eval 4).natAbs := by
  let : Fact p.Prime := ⟨hp⟩
  have hnz := root_nonzero hm hp hd
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hnz (by decide)
  have ho := ZMod.orderOf_dvd_card_sub_one hnz
  obtain ⟨k, he⟩ := root_order_decomposition hm hp hd
  cases k with
  | zero =>
    simp only [pow_zero, one_mul] at he
    have hlt := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) (hpm.trans (he ▸ ho))
    have := hp.two_le
    omega
  | succ k =>
    let d := p ^ k * orderOf (4 : ZMod p)
    have hmd : m = d * p := by rw [he]; dsimp [d]; ring
    have hdp : 0 < d := Nat.pos_of_mul_pos_right (hmd ▸ hm)
    have hr : (4 : ZMod p) ^ d = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      exact dvd_mul_left _ _
    have hxd : (p : ℤ) ∣ (4 : ℤ) ^ d - 1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simpa using sub_eq_zero.mpr hr
    have hxnot : ¬(p : ℤ) ∣ (4 : ℤ) ^ d := by
      intro hh
      have hh1 := dvd_sub hh hxd
      simp only [sub_sub_cancel] at hh1
      exact hp.not_dvd_one (by exact_mod_cast hh1)
    have hval := emultiplicity_geom_sum₂_eq_one (R := ℤ) (x := (4 : ℤ) ^ d) (y := 1)
      (Nat.prime_iff_prime_int.mp hp) (hp.odd_of_ne_two hp2) hxd hxnot
    have hnot := (emultiplicity_eq_coe.mp hval).2
    simp only [one_pow, mul_one] at hnot
    have hdm : d ∈ m.properDivisors := by
      rw [Nat.mem_properDivisors, hmd]
      exact ⟨dvd_mul_right _ _, by nlinarith [hp.two_le]⟩
    have hv := map_dvd (evalRingHom (4 : ℤ))
      (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hdm)
    simp only [coe_evalRingHom, eval_mul, eval_sub, eval_pow, eval_X, eval_one] at hv
    have hgeom : (4 : ℤ) ^ m - 1 =
        (4 ^ d - 1) * ∑ i ∈ Finset.range p, (4 ^ d) ^ i := by
      calc (4 : ℤ) ^ m - 1 = (4 ^ d) ^ p - 1 := by rw [hmd, pow_mul]
           _ = _ := (mul_geom_sum _ _).symm
    rw [hgeom] at hv
    have hxne : (4 : ℤ) ^ d - 1 ≠ 0 := by
      have hlt : (1 : ℤ) < 4 ^ d := one_lt_pow₀ (by norm_num) hdp.ne'
      omega
    have hdiv := (mul_dvd_mul_iff_left hxne).mp hv
    intro hh
    apply hnot
    apply dvd_trans _ hdiv
    exact_mod_cast (Int.natCast_dvd.mpr hh)

private theorem exists_prime_orderOf_four {m : ℕ} (hm : 1 < m) :
    ∃ p : ℕ, p.Prime ∧ orderOf (4 : ZMod p) = m := by
  let N := ((cyclotomic m ℤ).eval 4).natAbs
  have hbound : 3 ^ m.totient < N := by
    simpa [N] using sub_one_pow_totient_lt_natAbs_cyclotomic_eval
      (q := 4) hm (by decide)
  have hN : 1 < N := lt_of_le_of_lt (Nat.one_le_pow _ _ (by decide)) hbound
  by_contra h
  push Not at h
  have hall : ∀ p : ℕ, p.Prime → p ∣ N → p ∣ m := by
    intro p hp hd
    by_contra hpm
    let : Fact p.Prime := ⟨hp⟩
    let : NeZero (m : ZMod p) := NeZero.of_not_dvd (ZMod p) hpm
    exact h p hp ((isRoot_cyclotomic_iff.mp (root_of_dvd hd)).eq_orderOf.symm)
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hN.ne'
  have he : N = p ^ N.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (fun {q} hq hqd =>
      Nat.le_antisymm
        (prime_le_of_root (by omega) hp hd hq (hall q hq hqd))
        (prime_le_of_root (by omega) hq hqd hp (hall p hp hd)))
  have hnsq := prime_sq_not_dvd (by omega) hp hd (hall p hp hd)
  have hk : N.primeFactorsList.length ≤ 1 := by
    by_contra hh
    apply hnsq
    rw [show ((cyclotomic m ℤ).eval 4).natAbs = N from rfl, he]
    exact pow_dvd_pow p (by omega)
  have hle : N ≤ p := by
    calc N = p ^ N.primeFactorsList.length := he
         _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk
         _ = p := pow_one p
  have hphi : p - 1 ≤ m.totient := by
    rw [← Nat.totient_prime hp]
    exact Nat.le_of_dvd (Nat.totient_pos.mpr (by omega))
      (Nat.totient_dvd_of_dvd (hall p hp hd))
  have hpbound : p ≤ 3 ^ (p - 1) := by
    have hh := Nat.lt_pow_self (n := p - 1) (by decide : 1 < 3)
    have := hp.two_le
    omega
  have hle' := hpbound.trans (Nat.pow_le_pow_right (by decide) hphi)
  omega

/-- The binary primitive-prime existence theorem at exponent `4*n`, for odd
`n ≥ 3`: the multiplicative order itself certifies primitivity. -/
theorem exists_prime_orderOf_two_four_mul_odd {n : ℕ} (_hn : Odd n) (hn : 3 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = 4 * n := by
  obtain ⟨p, hp, horder⟩ := exists_prime_orderOf_four (m := 2 * n) (by omega)
  refine ⟨p, hp, ?_⟩
  have hsquare : (2 : ZMod p) ^ 2 = 4 := by ring
  have hd : 2 ∣ orderOf (2 : ZMod p) := by
    apply dvd_trans (show 2 ∣ orderOf ((2 : ZMod p) ^ 2) by rw [hsquare, horder]; omega)
    exact orderOf_pow_dvd 2
  have he := orderOf_pow_of_dvd (by decide : 2 ≠ 0) hd
  rw [hsquare, horder] at he
  have hmul := Nat.div_mul_cancel hd
  omega

end Theory.NumberTheory

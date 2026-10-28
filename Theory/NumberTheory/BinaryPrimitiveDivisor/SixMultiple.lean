module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Primitive binary primes at exponents divisible by six

For `n ≥ 2`, some prime `p` satisfies `orderOf (2 : ZMod p) = 6*n`.
The multiplicative order certifies that `p` divides `2^(6*n)-1` and does
not divide `2^i-1` for any positive `i < 6*n`.

We prove primitive-prime existence for all exponents `m ≥ 12`. A prime
factor `p` of `Φ_m(2)` gives `m = p^k * orderOf (2 : ZMod p)`. If it is
nonprimitive, it is the largest prime dividing `m`, and an odd-prime
geometric-sum valuation shows that its square does not divide `Φ_m(2)`.
Thus absence of a primitive prime would force `Φ_m(2) ≤ p`.

For the reverse inequality, put `d = orderOf (2 : ZMod p)` and
`x = 2^(p^(k-1))`. Cyclotomic expansion gives
`Φ_m(2) * Φ_d(x) = Φ_d(x^p)`. The standard bounds by `(x-1)^φ(d)`
and `(x+1)^φ(d)` show that the ratio exceeds `p` when `p ≥ 5`.
For `p = 3`, the order is two; `m ≥ 12` excludes `m = 6` and makes
`x ≥ 8`, giving the same strict inequality. The prime two cannot occur.

Sources: GLS2, Chapter A, Theorem 1.1
(`refs/KGroup/GLS2/ChapterA.tex`, lines 192–194), and the unitary use at
exponent `6*b` in GLS3 §6.5 (`refs/KGroup/GLS3/chapter6.tex`).
The prime-factor helpers adapt the base-four argument developed in
`Theory.NumberTheory.BinaryPrimitiveDivisor` to base two.
-/

public section

open Polynomial
namespace Theory.NumberTheory.SixMultiple

private theorem root_of_dvd {m p : ℕ}
    (hd : p ∣ ((cyclotomic m ℤ).eval 2).natAbs) :
    (cyclotomic m (ZMod p)).IsRoot 2 := by
  rw [IsRoot.def, ← map_cyclotomic_int m (ZMod p)]
  rw [eval_map, eval₂_at_ofNat]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
    (Int.natCast_dvd.mpr hd)

private theorem root_order_decomposition {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hd : p ∣ ((cyclotomic m ℤ).eval 2).natAbs) :
    ∃ k : ℕ, m = p ^ k * orderOf (2 : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, d, hpd, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.ne_one
  let : NeZero (d : ZMod p) := NeZero.of_not_dvd (ZMod p) hpd
  have hr := root_of_dvd hd
  rw [he] at hr
  have ho := (isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp hr).eq_orderOf
  exact ⟨k, by simpa only [← ho] using he⟩

private theorem root_nonzero {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hd : p ∣ ((cyclotomic m ℤ).eval 2).natAbs) : (2 : ZMod p) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hcop := coprime_of_root_cyclotomic (a := 2) hm (root_of_dvd hd)
  exact mt (ZMod.natCast_eq_zero_iff 2 p).mp (hp.coprime_iff_not_dvd.mp hcop.symm)

private theorem prime_le_of_root {m p q : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hd : p ∣ ((cyclotomic m ℤ).eval 2).natAbs) (hq : q.Prime) (hqm : q ∣ m) :
    q ≤ p := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, he⟩ := root_order_decomposition hm hp hd
  rw [he] at hqm
  rcases hq.dvd_mul.mp hqm with hqk | hqo
  · exact Nat.le_of_dvd hp.pos (hq.dvd_of_dvd_pow hqk)
  · have ho := ZMod.orderOf_dvd_card_sub_one (root_nonzero hm hp hd)
    exact (Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) (hqo.trans ho)).trans (Nat.sub_le _ _)

private theorem prime_sq_not_dvd {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hd : p ∣ ((cyclotomic m ℤ).eval 2).natAbs) (hpm : p ∣ m) :
    ¬p ^ 2 ∣ ((cyclotomic m ℤ).eval 2).natAbs := by
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
    let d := p ^ k * orderOf (2 : ZMod p)
    have hmd : m = d * p := by rw [he]; dsimp [d]; ring
    have hdp : 0 < d := Nat.pos_of_mul_pos_right (hmd ▸ hm)
    have hr : (2 : ZMod p) ^ d = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      exact dvd_mul_left _ _
    have hxd : (p : ℤ) ∣ (2 : ℤ) ^ d - 1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simpa using sub_eq_zero.mpr hr
    have hxnot : ¬(p : ℤ) ∣ (2 : ℤ) ^ d := by
      intro hh
      have hh1 := dvd_sub hh hxd
      simp only [sub_sub_cancel] at hh1
      exact hp.not_dvd_one (by exact_mod_cast hh1)
    have hval := emultiplicity_geom_sum₂_eq_one (R := ℤ) (x := (2 : ℤ) ^ d) (y := 1)
      (Nat.prime_iff_prime_int.mp hp) (hp.odd_of_ne_two hp2) hxd hxnot
    have hnot := (emultiplicity_eq_coe.mp hval).2
    simp only [one_pow, mul_one] at hnot
    have hdm : d ∈ m.properDivisors := by
      rw [Nat.mem_properDivisors, hmd]
      exact ⟨dvd_mul_right _ _, by nlinarith [hp.two_le]⟩
    have hv := map_dvd (evalRingHom (2 : ℤ))
      (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hdm)
    simp only [coe_evalRingHom, eval_mul, eval_sub, eval_pow, eval_X, eval_one] at hv
    have hgeom : (2 : ℤ) ^ m - 1 =
        (2 ^ d - 1) * ∑ i ∈ Finset.range p, (2 ^ d) ^ i := by
      calc (2 : ℤ) ^ m - 1 = (2 ^ d) ^ p - 1 := by rw [hmd, pow_mul]
           _ = _ := (mul_geom_sum _ _).symm
    rw [hgeom] at hv
    have hxne : (2 : ℤ) ^ d - 1 ≠ 0 := by
      have hlt : (1 : ℤ) < 2 ^ d := one_lt_pow₀ (by norm_num) hdp.ne'
      omega
    have hdiv := (mul_dvd_mul_iff_left hxne).mp hv
    intro hh
    apply hnot
    apply dvd_trans _ hdiv
    exact_mod_cast (Int.natCast_dvd.mpr hh)


private theorem eval_prime_pow_mul {p d : ℕ} (hp : p.Prime) (hpd : ¬p ∣ d)
    (k : ℕ) (x : ℝ) :
    (cyclotomic (p ^ (k + 1) * d) ℝ).eval x *
      (cyclotomic d ℝ).eval (x ^ (p ^ k)) =
      (cyclotomic d ℝ).eval (x ^ (p ^ (k + 1))) := by
  induction k generalizing x with
  | zero =>
    simpa [expand_eval, mul_comm] using
      (congrArg (eval x) (cyclotomic_expand_eq_cyclotomic_mul hp hpd ℝ)).symm
  | succ k ih =>
    have hdiv : p ∣ p ^ (k + 1) * d :=
      dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) d
    have he := congrArg (eval x) (cyclotomic_expand_eq_cyclotomic hp hdiv ℝ)
    have hindex : p ^ (k + 1) * d * p = p ^ (k + 1 + 1) * d := by ring
    simp only [expand_eval, hindex] at he
    rw [← he]
    simpa only [← pow_mul, ← pow_succ'] using ih (x ^ p)

private theorem pow_growth {p : ℕ} (hp : 5 ≤ p) {x : ℝ} (hx : 2 ≤ x) :
    (p : ℝ) * (x + 1) < x ^ p - 1 := by
  induction p, hp using Nat.le_induction with
  | base =>
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 4
    norm_num at hh ⊢
    nlinarith [mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ x ^ 4 - 16 by linarith)]
  | succ p hp ih =>
    have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith [mul_nonneg (show 0 ≤ x - 2 by linarith) (show 0 ≤ x ^ p by positivity)]

private theorem cyclotomic_ratio_gt {d p : ℕ} (hd : 2 ≤ d) (hp : 1 ≤ p)
    {x : ℝ} (hx : 1 < x) (hg : (p : ℝ) * (x + 1) < x ^ p - 1) :
    (p : ℝ) * (cyclotomic d ℝ).eval x < (cyclotomic d ℝ).eval (x ^ p) := by
  have ht : 0 < d.totient := Nat.totient_pos.mpr (by omega)
  have hxp : 1 < x ^ p := one_lt_pow₀ hx (by omega)
  have hl := sub_one_pow_totient_lt_cyclotomic_eval hd hxp
  have hu := cyclotomic_eval_le_add_one_pow_totient hx d
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hple : (p : ℝ) ≤ (p : ℝ) ^ d.totient :=
    le_self_pow₀ hp' ht.ne'
  calc
    (p : ℝ) * (cyclotomic d ℝ).eval x ≤ p * (x + 1) ^ d.totient := by gcongr
    _ ≤ (p : ℝ) ^ d.totient * (x + 1) ^ d.totient := by gcongr
    _ = ((p : ℝ) * (x + 1)) ^ d.totient := (mul_pow _ _ _).symm
    _ < (x ^ p - 1) ^ d.totient := by gcongr
    _ < (cyclotomic d ℝ).eval (x ^ p) := hl


private theorem cyclotomic_gt_nonprimitive {m p : ℕ} (hm : 12 ≤ m) (hp : p.Prime)
    (hdvd : p ∣ ((cyclotomic m ℤ).eval 2).natAbs) (hpm : p ∣ m) :
    p < ((cyclotomic m ℤ).eval 2).natAbs := by
  let : Fact p.Prime := ⟨hp⟩
  have hnz := root_nonzero (by omega) hp hdvd
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hnz (by decide)
  obtain ⟨k, he⟩ := root_order_decomposition (by omega) hp hdvd
  have ho := ZMod.orderOf_dvd_card_sub_one hnz
  have hpos : 0 < orderOf (2 : ZMod p) := by
    by_contra h
    have hh : orderOf (2 : ZMod p) = 0 := by omega
    simp [hh] at he
    omega
  have hle : orderOf (2 : ZMod p) ≤ p - 1 :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) ho
  have hnot : ¬p ∣ orderOf (2 : ZMod p) := by
    intro h
    have := Nat.le_of_dvd hpos h
    omega
  have hd : 2 ≤ orderOf (2 : ZMod p) := by
    have hn1 : orderOf (2 : ZMod p) ≠ 1 := by
      intro h
      have hh := orderOf_eq_one_iff.mp h
      have hh' : (1 : ZMod p) = 0 := by linear_combination hh
      exact one_ne_zero hh'
    omega
  cases k with
  | zero =>
    simp only [pow_zero, one_mul] at he
    exact False.elim (hnot (he ▸ hpm))
  | succ k =>
    let x : ℝ := 2 ^ (p ^ k)
    have hx : 2 ≤ x := le_self_pow₀ (by norm_num) (pow_ne_zero k hp.ne_zero)
    have hx1 : 1 < x := by linarith
    have hg : (p : ℝ) * (x + 1) < x ^ p - 1 := by
      by_cases hp3 : p = 3
      · subst p
        have ho3 : orderOf (2 : ZMod 3) = 2 := by omega
        rw [ho3] at he
        have hk : k ≠ 0 := by
          intro hh
          subst k
          norm_num at he
          omega
        have hk3 : 3 ≤ 3 ^ k := Nat.le_self_pow hk 3
        have hx8 : 8 ≤ x := by
          have := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk3)
          norm_num at this
          exact this
        norm_num
        nlinarith [mul_nonneg (show 0 ≤ x - 2 by linarith) (sq_nonneg x)]
      · have hp5 : 5 ≤ p := by
          obtain ⟨a, ha⟩ := hp.odd_of_ne_two hp2
          have hpge := hp.two_le
          omega
        exact pow_growth hp5 hx
    have hi := eval_prime_pow_mul hp hnot k (2 : ℝ)
    rw [← he] at hi
    have hxp : x ^ p = (2 : ℝ) ^ (p ^ (k + 1)) := by
      dsimp [x]
      rw [← pow_mul, ← pow_succ]
    have hr := cyclotomic_ratio_gt hd hp.pos hx1 hg
    rw [hxp, ← hi] at hr
    have hden := cyclotomic_pos' (orderOf (2 : ZMod p)) hx1
    have hb : (p : ℝ) < (cyclotomic m ℝ).eval 2 := by
      nlinarith
    have heval : ((((cyclotomic m ℤ).eval 2).natAbs : ℕ) : ℝ) =
        (cyclotomic m ℝ).eval 2 := by
      rw [Nat.cast_natAbs, abs_of_pos]
      · simpa using (cyclotomic.eval_apply (2 : ℤ) m (Int.castRingHom ℝ)).symm
      · exact_mod_cast cyclotomic_pos' m (by norm_num : (1 : ℤ) < 2)
    rw [← heval] at hb
    exact_mod_cast hb

private theorem exists_prime_orderOf_two {m : ℕ} (hm : 12 ≤ m) :
    ∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = m := by
  let N := ((cyclotomic m ℤ).eval 2).natAbs
  have hN : 1 < N := by
    simpa [N] using sub_one_pow_totient_lt_natAbs_cyclotomic_eval
      (q := 2) (by omega : 1 < m) (by decide)
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
    rw [show ((cyclotomic m ℤ).eval 2).natAbs = N from rfl, he]
    exact pow_dvd_pow p (by omega)
  have hle : N ≤ p := by
    calc N = p ^ N.primeFactorsList.length := he
         _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk
         _ = p := pow_one p
  exact (cyclotomic_gt_nonprimitive hm hp hd (hall p hp hd)).not_ge hle

end Theory.NumberTheory.SixMultiple

namespace Theory.NumberTheory

/-- A primitive prime divisor of `2^(6*n)-1`, expressed by its exact
multiplicative order. The bound `6*n ≥ 12` avoids both exceptional exponents
in GLS2, Chapter A, Theorem 1.1. -/
theorem exists_prime_orderOf_two_six_mul {n : ℕ} (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ orderOf (2 : ZMod p) = 6 * n :=
  SixMultiple.exists_prime_orderOf_two (by omega)

end Theory.NumberTheory

module

public import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# An obstruction prime outside the scalar center

If an even prime power `q` has no prime divisor of `q+1` other than 5, then
`q = 2^e` and `q+1 = 5^k`. For `e ≥ 3`, reduction modulo 8 forces `k` even,
while reduction modulo 3 rules out even `k`. The small exponents leave only
`q = 4`. This supplies an odd prime different from 5 for the diagonal torus
in the unitary-five parabolic, including when `q = 2`.

Source motivation: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.12, final paragraph (printed p. 264). This elementary arithmetic permits
that paragraph's existential obstruction without a 5-primary torus quotient.
-/

public section

namespace Theory.SpecificGroups.UnitaryFive

/-- An even prime power other than 4 has an odd prime divisor of `q+1` different from 5. -/
theorem exists_odd_prime_ne_five_dvd_succ {q : ℕ} (hq : IsPrimePow q) (heven : Even q) (hne : q ≠ 4) :
    ∃ p, p.Prime ∧ Odd p ∧ p ∣ q + 1 ∧ p ≠ 5 := by
  obtain ⟨r, e, hr, he, hq⟩ := (isPrimePow_nat_iff q).mp hq
  have hr2 : 2 = r := Nat.prime_eq_prime_of_dvd_pow Nat.prime_two hr
    (hq ▸ even_iff_two_dvd.mp heven)
  subst r
  subst q
  have hlarge : 2 ≤ 2 ^ e := Nat.le_pow he
  suffices ∃ p, p.Prime ∧ p ∣ 2 ^ e + 1 ∧ p ≠ 5 by
    obtain ⟨p, hp, hd, hn⟩ := this
    refine ⟨p, hp, ?_, hd, hn⟩
    rcases hp.eq_two_or_odd with h | h
    · subst p
      obtain ⟨a, ha⟩ := heven
      obtain ⟨b, hb⟩ := hd
      omega
    · exact Nat.odd_iff.mpr h
  by_contra h
  push Not at h
  obtain ⟨s, hs, hd⟩ := Nat.exists_prime_and_dvd (show 2 ^ e + 1 ≠ 1 by omega)
  have hs5 := h s hs hd
  subst s
  have hpp : IsPrimePow (2 ^ e + 1) := isPrimePow_iff_unique_prime_dvd.mpr
    ⟨5, ⟨hs, hd⟩, fun p hp => h p hp.1 hp.2⟩
  obtain ⟨s, k, hs, hk, hpow⟩ := (isPrimePow_nat_iff _).mp hpp
  have hs5 : s = 5 := h s hs (hpow ▸ dvd_pow_self s hk.ne')
  subst s
  have he3 : 3 ≤ e := by
    have hn1 : e ≠ 1 := by
      intro he1
      subst e
      norm_num at hd
    have hn2 : e ≠ 2 := by
      intro he2
      subst e
      exact hne rfl
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le he3
  have hmod8 : (5 : ZMod 8) ^ k = 1 := by
    have hm := congrArg (fun n : ℕ => (n : ZMod 8)) hpow
    rw [hd, pow_add] at hm
    norm_num at hm
    simpa only [show (8 : ZMod 8) = 0 by decide, zero_mul, zero_add] using hm
  rcases Nat.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have hm := congrArg (fun n : ℕ => (n : ZMod 3)) hpow
    push_cast at hm
    rw [← two_mul t, pow_mul] at hm
    norm_num at hm
    rw [show (25 : ZMod 3) = 1 by decide, one_pow] at hm
    have hz : (2 : ZMod 3) ^ e = 0 := by linear_combination -hm
    exact (pow_ne_zero e (by decide : (2 : ZMod 3) ≠ 0)) hz
  · rw [pow_add, pow_mul] at hmod8
    norm_num at hmod8
    rw [show (25 : ZMod 8) = 1 by decide, one_pow, one_mul] at hmod8
    exact (by decide : (5 : ZMod 8) ≠ 1) hmod8

end Theory.SpecificGroups.UnitaryFive

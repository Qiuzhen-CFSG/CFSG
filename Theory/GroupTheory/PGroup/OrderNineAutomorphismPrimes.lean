module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Group.Action.End
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Prime divisors of small three-group automorphism groups

For an automorphism of prime order q, orbit counting gives
|Q| ≡ |C_Q(q)| modulo q. When |Q| ≤ 9 is a power of three, a nonidentity
automorphism has a proper fixed subgroup and q divides one of 2, 6, or 8.
Thus the automorphism group has no prime divisor other than two or three.

This supplies the final order restriction in Aschbacher–Smith,
*The Classification of Quasithin Groups*, A.1.25(3), printed p.25.
-/

open Subgroup

/-- Only two and three divide the automorphism-group order of a three-group
of order at most nine. -/
public theorem prime_dvd_mulAut_card_le_nine
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 3 Q)
    (hc : Nat.card Q ≤ 9) {q : ℕ} (hq : q.Prime)
    (hd : q ∣ Nat.card (MulAut Q)) : q = 2 ∨ q = 3 := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' q hd
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hnle : n ≤ 2 := by
    by_contra! hh
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 3) hh
    rw [← hn] at hpow
    norm_num at hpow
    omega
  let A := zpowers a
  have hA : IsPGroup q A := IsPGroup.of_card (n := 1) (by simp [A, ha])
  let F := FixedPoints.subgroup A Q
  have hmod := hA.card_modEq_card_fixedPoints Q
  change Nat.card Q ≡ Nat.card F [MOD q] at hmod
  obtain ⟨k, hk, hF⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (hn ▸ F.card_subgroup_dvd_card)
  have hkn : k < n := by
    by_contra! hle
    have hkeq : k = n := by omega
    have heq : Nat.card F = Nat.card Q := by rw [hF, hkeq, hn]
    have htop := F.eq_top_of_card_eq heq
    have ha1 : a = 1 := by
      apply MulEquiv.ext
      intro x
      exact (show x ∈ F from htop ▸ mem_top x) ⟨a, mem_zpowers a⟩
    rw [ha1, orderOf_one] at ha
    exact hq.ne_one ha.symm
  have hdif : q ∣ 3 ^ n - 3 ^ k := by
    simpa only [hn, hF] using hmod.symm.dvd'
  have hqgt := hq.one_lt
  interval_cases n <;> interval_cases k <;> norm_num at *
  all_goals
    have hd24 : q ∣ 2 ^ 3 * 3 := hdif.trans (by norm_num)
    rcases hq.dvd_mul.mp hd24 with hd2 | hd3
    · exact Or.inl (((Nat.dvd_prime Nat.prime_two).mp (hq.dvd_of_dvd_pow hd2)).resolve_left hq.ne_one)
    · exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp hd3).resolve_left hq.ne_one)


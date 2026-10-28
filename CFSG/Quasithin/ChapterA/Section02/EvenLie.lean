module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ParabolicRestrictions
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.ParabolicSections
public import Theory.PrimeRank
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Arithmetic restrictions in the characteristic-two Lie-type case

These are the field-size deductions in Aschbacher--Smith, *The Classification
of Quasithin Groups*, combined manuscript (1 March 2004), Lemma A.2.18,
printed p. 40. The group-theoretic input to the split-torus deduction is
stated as a prime-rank bound. The fixed-field size is denoted by `q`, also for
unitary groups.
-/

namespace CFSG.Quasithin.ChapterA.Section02.EvenLie

/-- If the odd prime divisors of `q - 1` are excluded, an even field size is two. -/
public theorem field_size_eq_two_of_no_odd_torus_prime
    {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ q - 1 → p = 2) : q = 2 := by
  have hsub : q - 1 = 1 := Nat.eq_one_iff_not_exists_prime_dvd.mpr (by
    intro p hp hpdvd
    have hp2 := hprime p hp hpdvd
    subst p
    rcases hq with ⟨k, hk⟩
    subst q
    rcases hpdvd with ⟨m, hm⟩
    omega)
  omega

/-- The rank-three split torus rules out `q > 2` when every odd-prime rank
of the containing two-local subgroup is at most two. -/
public theorem field_size_eq_two_of_split_torus_rank
    {G : Type*} [Group G] {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q)
    (htorus : ∀ p : ℕ, p.Prime → p ∣ q - 1 → p ≠ 2 → 3 ≤ primeRank p G)
    (hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → primeRank p G ≤ 2) : q = 2 := by
  apply field_size_eq_two_of_no_odd_torus_prime hq hq2
  intro p hp hpdvd
  by_contra hp2
  exact (Nat.not_succ_le_self 2) ((htorus p hp hpdvd hp2).trans (hrank p hp hp2))

/-- The `U₅(q)` parabolic restriction `q + 1 = gcd(q + 1, 5)` leaves only
the fixed-field size four in characteristic two. -/
public theorem unitary_five_field_size_eq_four
    {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q)
    (hparabolic : q + 1 = Nat.gcd (q + 1) 5) : q = 4 := by
  have hbound : q + 1 ≤ 5 := by
    rw [hparabolic]
    exact Nat.gcd_le_right _ (by omega)
  have hq4 : q ≤ 4 := by omega
  interval_cases q <;> norm_num at *

/-- The prime-rank obstruction in the `U₅(q)` parabolic first makes its
cyclic factor trivial, and therefore fixes `q = 4`. -/
public theorem unitary_five_field_size_eq_four_of_parabolic_rank
    {G : Type*} [Group G] {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q)
    (hparabolic : ∀ p : ℕ, p.Prime →
      p ∣ (q + 1) / Nat.gcd (q + 1) 5 → 3 ≤ primeRank p G)
    (hrank : ∀ p : ℕ, p.Prime → primeRank p G ≤ 2) : q = 4 := by
  let d := Nat.gcd (q + 1) 5
  have hquot : (q + 1) / d = 1 := Nat.eq_one_iff_not_exists_prime_dvd.mpr (by
    intro p hp hpdvd
    exact (Nat.not_succ_le_self 2)
      ((hparabolic p hp hpdvd).trans (hrank p hp)))
  have hdvd : d ∣ q + 1 := Nat.gcd_dvd_left _ _
  have heq : q + 1 = d := by
    calc
      q + 1 = (q + 1) / d * d := (Nat.div_mul_cancel hdvd).symm
      _ = d := by rw [hquot, one_mul]
  exact unitary_five_field_size_eq_four hq hq2 heq

end CFSG.Quasithin.ChapterA.Section02.EvenLie

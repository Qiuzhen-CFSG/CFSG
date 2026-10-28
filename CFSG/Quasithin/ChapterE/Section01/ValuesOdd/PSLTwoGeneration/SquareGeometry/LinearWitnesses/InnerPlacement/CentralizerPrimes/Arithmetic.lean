module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# Odd primes in the prime-square torus

The two halves (p-1)/2 and (p+1)/2 are consecutive. For odd p at least
five, the odd half exceeds one. A prime divisor of that half divides
(p²-1)/2 and cannot divide twice the opposite side p-1 or p+1.
The endpoint p = 5 uses the odd half three.

These arithmetic facts are consumed by the actual dihedral, S₄ and PGL₂(p)
overgroup centralizers in `CentralizerPrimes.lean`.
Source: the prime-square case of Aschbacher--Smith E.1.14(6), printed p.214,
with the models of A.2.3(2), printed p.33.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.CentralizerPrimes

private theorem square_half_factor {p : ℕ} (hp : Odd p) :
    (p ^ 2 - 1) / 2 = 2 * ((p - 1) / 2) * ((p + 1) / 2) := by
  obtain ⟨a, rfl⟩ := hp
  have hm : (2 * a + 1 - 1) / 2 = a := by omega
  have hp : (2 * a + 1 + 1) / 2 = a + 1 := by omega
  rw [hm, hp]
  have he : (2 * a + 1) ^ 2 - 1 = 2 * (2 * a * (a + 1)) := by
    have hh : (2 * a + 1) ^ 2 = 2 * (2 * a * (a + 1)) + 1 := by ring
    omega
  rw [he, Nat.mul_div_right _ (by decide : 0 < 2)]

private theorem prime_of_odd {n : ℕ} (hn : Odd n) (hlarge : 1 < n) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∣ n := by
  obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  refine ⟨r, hr, ?_, hrn⟩
  rcases hr.eq_two_or_odd with rfl | ho
  · exact (hn.not_two_dvd_nat hrn).elim
  · exact Nat.odd_iff.mpr ho

/-- The odd half opposite an even half supplies a prime absent from twice
that side of the field order. The endpoint p = 5 is included. -/
theorem opposite_half_prime {p c : ℕ} (hp : Odd p) (hlarge : 5 ≤ p)
    (hc : (Even ((p - 1) / 2) ∧ c ∣ 2 * (p - 1)) ∨
      (Even ((p + 1) / 2) ∧ c ∣ 2 * (p + 1))) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∣ (p ^ 2 - 1) / 2 ∧ ¬ r ∣ c := by
  have hp2 : p = 2 * ((p - 1) / 2) + 1 := by
    obtain ⟨a, ha⟩ := hp
    omega
  have hhalves : (p + 1) / 2 = (p - 1) / 2 + 1 := by omega
  have hm : 2 ≤ (p - 1) / 2 := by omega
  have hplus : 3 ≤ (p + 1) / 2 := by omega
  rcases hc with ⟨he, hd⟩ | ⟨he, hd⟩
  · have ho : Odd ((p + 1) / 2) := by
      obtain ⟨a, ha⟩ := he
      exact ⟨a, by omega⟩
    obtain ⟨r, hr, hro, hrh⟩ := prime_of_odd ho (by omega)
    refine ⟨r, hr, hro, ?_, ?_⟩
    · rw [square_half_factor hp]
      exact hrh.trans (dvd_mul_left _ _)
    · intro hrc
      have hrm : r ∣ (p - 1) / 2 := by
        have hh : 2 * (p - 1) = 2 * (2 * ((p - 1) / 2)) := by omega
        have hhdiv := hrc.trans hd
        rw [hh] at hhdiv
        have hr2 : ¬ r ∣ 2 := by
          intro h
          have heq : r = 2 := le_antisymm (Nat.le_of_dvd (by decide) h) hr.two_le
          subst r
          exact hro.not_two_dvd_nat (dvd_refl 2)
        exact (hr.dvd_mul.mp ((hr.dvd_mul.mp hhdiv).resolve_left hr2)).resolve_left hr2
      have h1 : r ∣ 1 := by
        have := Nat.dvd_sub hrh hrm
        simpa only [hhalves, Nat.add_sub_cancel_left] using this
      exact hr.not_dvd_one h1
  · have ho : Odd ((p - 1) / 2) := by
      obtain ⟨a, ha⟩ := he
      exact ⟨a - 1, by omega⟩
    obtain ⟨r, hr, hro, hrh⟩ := prime_of_odd ho (by omega)
    refine ⟨r, hr, hro, ?_, ?_⟩
    · rw [square_half_factor hp]
      exact hrh.trans ((dvd_mul_left _ _).trans (dvd_mul_right _ _))
    · intro hrc
      have hrm : r ∣ (p + 1) / 2 := by
        have hh : 2 * (p + 1) = 2 * (2 * ((p + 1) / 2)) := by omega
        have hhdiv := hrc.trans hd
        rw [hh] at hhdiv
        have hr2 : ¬ r ∣ 2 := by
          intro h
          have hrEq : r = 2 := le_antisymm (Nat.le_of_dvd (by decide) h) hr.two_le
          subst r
          exact hro.not_two_dvd_nat (dvd_refl 2)
        exact (hr.dvd_mul.mp ((hr.dvd_mul.mp hhdiv).resolve_left hr2)).resolve_left hr2
      have h1 : r ∣ 1 := by
        have := Nat.dvd_sub hrm hrh
        simpa only [hhalves, Nat.add_sub_cancel_left] using this
      exact hr.not_dvd_one h1

/-- For odd p at least five the prime-square torus has a nontrivial odd
prime divisor; it cannot divide either four or eight. -/
theorem torus_prime {p : ℕ} (hp : Odd p) (hlarge : 5 ≤ p) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∣ (p ^ 2 - 1) / 2 := by
  have hc : (Even ((p - 1) / 2) ∧ 1 ∣ 2 * (p - 1)) ∨
      (Even ((p + 1) / 2) ∧ 1 ∣ 2 * (p + 1)) := by
    rcases Nat.even_or_odd ((p - 1) / 2) with he | ho
    · exact Or.inl ⟨he, one_dvd _⟩
    · right
      refine ⟨?_, one_dvd _⟩
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := ho
      exact ⟨b + 1, by omega⟩
  obtain ⟨r, hr, ho, hd, _⟩ := opposite_half_prime hp hlarge hc
  exact ⟨r, hr, ho, hd⟩
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.CentralizerPrimes

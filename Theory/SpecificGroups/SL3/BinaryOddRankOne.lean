module
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero

/-!
# Binary SL₃ with odd-prime ranks at most one

For a binary field larger than F₂, an odd prime divides its multiplicative
order. The two independent diagonal torus coordinates give an elementary
abelian plane at that prime. Thus SL₃ over a binary field has all odd-prime
ranks at most one only when the field has two elements.

The point-selection application uses this on the literal component image,
without passing through a projective quotient or dropping a scalar kernel.
Source: Aschbacher--Smith A.3.8(3) and 10.1.1, printed pp.45--46 and741.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.SL3.BinaryOddRankOne

/-- The split diagonal torus forces binary degree one. -/
theorem degree_eq_one_of_odd_primeRanks_le_one
    (F : Type*) [Field F] [Finite F] {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card F = 2 ^ n)
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p SL(3,F) ≤ 1) : n = 1 := by
  by_contra hd
  have hd2 : 2 ≤ n := by omega
  have hpow : 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hd2
  have he : Even (2 ^ n) := Nat.even_pow.mpr ⟨by decide,by omega⟩
  have ho : Odd (2 ^ n - 1) := Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)
  obtain ⟨p,hp,hpdiv⟩ := Nat.exists_prime_and_dvd (by omega : 2 ^ n - 1 ≠ 1)
  have hpo : Odd p := by
    rcases hp.eq_two_or_odd with rfl | h
    · exact (ho.not_two_dvd_nat hpdiv).elim
    · exact Nat.odd_iff.mpr h
  let : Fact p.Prime := ⟨hp⟩
  have hunit : 1 ≤ primeRank p Fˣ := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hz
    apply PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    simpa only [Nat.card_units,hcard] using hpdiv
  have htorus : 2 ≤ primeRank p (Fˣ × Fˣ) := by
    rw [primeRank_prod_eq_add p]
    omega
  have hsl : 2 ≤ primeRank p SL(3,F) := htorus.trans
    (Theory.GroupTheory.primeRank_le_of_injective p (Matrix.PSL3.CartanActions.torusSL F)
      (Matrix.PSL3.CartanActions.BorelQuotient.torusSL_injective F))
  have := hr p hp hpo
  omega


end Matrix.SL3.BinaryOddRankOne

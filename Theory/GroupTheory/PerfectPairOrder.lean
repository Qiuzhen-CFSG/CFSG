module
public import Theory.GroupTheory.PerfectPairPrimeRank
public import Mathlib.Data.Nat.Squarefree

/-!
# Order obstructions to a pair of perfect factors

If a finite group order divides 2ᵃqᵇc with c squarefree, every odd prime
rank away from q is at most one. Burnside's two-prime theorem therefore
prevents it from containing two copies of all odd ranks of a nontrivial
perfect group. The conclusion uses divisibility, so it applies unchanged
to central quotients and to groups embedded in a certified finite model.

Source: Lagrange's theorem and Burnside's two-prime theorem, used in
Aschbacher--Smith 4.4.12, printed p.622.
-/

public section
open Subgroup
namespace Theory.GroupTheory
/-- Outside the two distinguished primes, a squarefree remaining order
factor forces prime rank at most one. -/
theorem primeRank_le_one_of_card_dvd_two_prime_squarefree
    (H : Type*) [Group H] [Finite H] {q p a b c : ℕ}
    (hq : q.Prime) [Fact p.Prime] (ho : Odd p) (hne : p ≠ q)
    (hc : Squarefree c) (hd : Nat.card H ∣ 2 ^ a * q ^ b * c) :
    primeRank p H ≤ 1 := by
  apply primeRank_le_one_of_square_not_dvd
  intro hsq
  have hp : p.Prime := Fact.out
  have h2 : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr
    (by
      intro h
      have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
      subst p
      exact ho.not_two_dvd_nat (dvd_refl 2))
  have hq' : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr
    (fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
  have hcop : Nat.Coprime (p ^ 2) (2 ^ a * q ^ b) :=
    ((h2.pow_right a).mul_right (hq'.pow_right b)).pow_left 2
  have hpc := hcop.dvd_mul_left.mp (hsq.trans hd)
  exact (Nat.squarefree_iff_prime_squarefree.mp hc p hp) (by simpa only [pow_two] using hpc)

/-- A two-prime power times a squarefree factor cannot contain doubled
odd ranks of a nontrivial perfect group. -/
theorem Perfect.no_doubled_odd_ranks_of_order
    (S H : Type*) [Group S] [Finite S] [Nontrivial S] [Group.IsPerfect S]
    [Group H] [Finite H] {q a b c : ℕ} (hq : q.Prime)
    (hc : Squarefree c) (hcard : Nat.card H ∣ 2 ^ a * q ^ b * c)
    (hd : ∀ p : ℕ, p.Prime → Odd p → 2 * primeRank p S ≤ primeRank p H) : False := by
  apply Perfect.no_doubled_odd_ranks S H hq hd
  intro p hp ho hne
  let : Fact p.Prime := ⟨hp⟩
  exact primeRank_le_one_of_card_dvd_two_prime_squarefree H hq ho hne hc hcard
end Theory.GroupTheory

module
public import Theory.GroupTheory.TwoPrimeSolvable
public import Theory.GroupTheory.PrimeRankSquareFree
public import Theory.GroupTheory.PrimeRankZero
public import Mathlib.GroupTheory.IsPerfect

/-!
# Odd ranks of a doubled perfect group

Burnside's two-prime theorem forces a nontrivial perfect finite group to
have an odd prime divisor outside any prescribed prime. Thus two copies
of its odd ranks cannot fit in a finite group whose odd ranks are at most
one away from that prime. This obstruction applies to literal component
quotients and to perfect subgroups of unitary parabolics.

Source: Burnside's two-prime theorem; the component inspection in
Aschbacher--Smith 4.4.12, printed p.622.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- A nontrivial perfect finite group has an odd prime divisor distinct
from any prescribed prime. -/
theorem Perfect.exists_odd_prime_ne_dvd_card
    (S : Type*) [Group S] [Finite S] [Nontrivial S] [Group.IsPerfect S]
    {q : ℕ} (hq : q.Prime) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ≠ q ∧ p ∣ Nat.card S := by
  by_contra! h
  apply Group.IsPerfect.not_isSolvable S
  apply isSolvable_of_prime_dvd_card_eq_two_or_prime S hq
  intro p hp hd
  by_cases htwo : p = 2
  · exact Or.inl htwo
  · exact Or.inr (by
      by_contra hne
      exact h p hp (hp.odd_of_ne_two htwo) hne hd)

/-- Two copies of the odd ranks of a nontrivial perfect group cannot fit
in a group with odd rank at most one away from a single prime. -/
theorem Perfect.no_doubled_odd_ranks
    (S H : Type*) [Group S] [Finite S] [Nontrivial S] [Group.IsPerfect S]
    [Group H] [Finite H] {q : ℕ} (hq : q.Prime)
    (hd : ∀ p : ℕ, p.Prime → Odd p → 2 * primeRank p S ≤ primeRank p H)
    (hb : ∀ p : ℕ, p.Prime → Odd p → p ≠ q → primeRank p H ≤ 1) : False := by
  obtain ⟨p,hp,ho,hne,hpS⟩ := Perfect.exists_odd_prime_ne_dvd_card S hq
  let : Fact p.Prime := ⟨hp⟩
  have hpos : primeRank p S ≠ 0 := fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hpS
  have hlow := hd p hp ho
  have hupp := hb p hp ho hne
  omega

end Theory.GroupTheory

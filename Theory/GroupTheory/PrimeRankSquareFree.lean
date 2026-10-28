module
public import Theory.GroupTheory.PrimeRankCyclicSylow

/-!
# Prime rank when the group order has no prime square

A Sylow p-subgroup then has order one or p, so it is cyclic and the
ambient p-rank is at most one. This supplies the finite-order rows in
Aschbacher–Smith C.4.8 specialized to a nonnormal A₅ component pair.
-/

public section
open Subgroup
/-- Absence of a prime square bounds prime rank by one. -/
theorem primeRank_le_one_of_square_not_dvd {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (h : ¬ p ^ 2 ∣ Nat.card G) : primeRank p G ≤ 1 := by
  let P : Sylow p G := Classical.choice inferInstance
  apply P.primeRank_le_one_of_isCyclic
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! hh
    exact h ((pow_dvd_pow p hh).trans (hn ▸ (P : Subgroup G).card_subgroup_dvd_card))
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [hn]
  simpa only [pow_one] using pow_dvd_pow p hnle


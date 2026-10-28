module
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Prime rank from the prime part of the group order

If the order of a finite group is not divisible by `p^(n+1)`, every
elementary abelian p-subgroup has order at most `p^n`. The elementary
characterization of prime rank then bounds the group's p-rank by n.
This is the usual Lagrange bound, used for the small finite models in
Aschbacher--Smith 4.4.12, printed p.622.
-/

public section
namespace Theory.GroupTheory

/-- Absence of the next prime power bounds the corresponding prime rank. -/
theorem primeRank_le_of_prime_pow_not_dvd {G : Type*} [Group G] [Finite G]
    {p n : ℕ} [Fact p.Prime] (hc : ¬ p ^ (n + 1) ∣ Nat.card G) :
    primeRank p G ≤ n := by
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro E hE
  let := hE
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p E).exists_card_eq
  have hkn : k ≤ n := by
    by_contra! h
    exact hc ((pow_dvd_pow p (by omega : n + 1 ≤ k)).trans
      (hk ▸ E.card_subgroup_dvd_card))
  rw [hk]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hkn

end Theory.GroupTheory

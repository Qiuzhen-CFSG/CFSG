module

public import Theory.ElementaryAbelian.GeneratorRank

/-!
# Prime rank when the group order has no prime cube

If `p³` does not divide the order of a finite group, its `p`-rank is at most
two. Every abelian `p`-subgroup has order at most `p²`; it is either cyclic
or elementary abelian of order `p²`. A vector-space basis gives two generators
in the latter case.

This elementary order bound supplies several of the quasithin examples in
Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem 0.1.2,
printed p.4. It is a rank bound, not a recognition theorem from group order.
-/

open scoped IsMulCommutative

private theorem rank_le_one_of_cyclic {G : Type*} [Group G] [Group.FG G]
    (hG : IsCyclic G) : Group.rank G ≤ 1 := by
  classical
  obtain ⟨g, hg⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := G)).mp hG
  have h : Subgroup.closure (({g} : Finset G) : Set G) = ⊤ := by
    simpa only [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure] using hg
  simpa only [Finset.card_singleton] using Group.rank_le h

/-- Absence of a prime cube in the order bounds the corresponding prime rank. -/
public theorem primeRank_le_two_of_cube_not_dvd {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hc : ¬ p ^ 3 ∣ Nat.card G) : primeRank p G ≤ 2 := by
  apply csSup_le'
  rintro n ⟨A, hAp, hAc, hfg, hn⟩
  let : IsMulCommutative A := hAc
  have hp : p.Prime := Fact.out
  obtain ⟨a, ha⟩ := hAp.exists_card_eq
  have hsmall : a ≤ 2 := by
    by_contra! h
    exact hc ((ha ▸ pow_dvd_pow p (by omega : 3 ≤ a)).trans A.card_subgroup_dvd_card)
  by_cases hcyc : IsCyclic A
  · exact hn.trans ((rank_le_one_of_cyclic hcyc).trans (by decide))
  have ha2 : a = 2 := by
    by_contra h
    have had : a ≤ 1 := by omega
    have hdiv : Nat.card A ∣ p := by
      rw [ha]
      simpa using pow_dvd_pow p had
    exact hcyc (isCyclic_of_card_dvd_prime hdiv)
  have hcard : Nat.card A = p ^ 2 := by simpa [ha2] using ha
  let : IsElementaryAbelian p A := {
    exponent_dvd_p := ((not_isCyclic_iff_exponent_eq_prime hp hcard).mp hcyc).dvd }
  exact hn.trans (IsElementaryAbelian.rank_le_of_card_le A hcard.le)

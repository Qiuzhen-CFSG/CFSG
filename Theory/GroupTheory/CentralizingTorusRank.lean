module

public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero

/-!
# Independent rank from a centralizing torus

A finite torus with nontrivial p-part and a disjoint commuting subgroup of
p-rank at least two have a join of p-rank at least three. When the latter
subgroup centralizes a third subgroup on which the torus acts faithfully,
the required disjointness follows from that faithful action.

Source application: Aschbacher–Smith, 10.2.3, printed p.747.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem three_le_primeRank_of_disjoint_commuting
    (D K : Subgroup G) {p : ℕ} [Fact p.Prime]
    (hd : Disjoint D K) (hc : D ≤ centralizer (K : Set G))
    (hD : p ∣ Nat.card D) (hK : 2 ≤ primeRank p K) :
    3 ≤ primeRank p (D ⊔ K : Subgroup G) := by
  have hDpos : 1 ≤ primeRank p D := by
    by_contra hn
    have hz : primeRank p D = 0 := by omega
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz hD
  rw [D.primeRank_sup_eq_add_of_disjoint_commuting K hd hc]
  omega

omit [Finite G] in
theorem disjoint_of_centralizes_faithful_subgroup
    (D K S : Subgroup G) (hfaithful : D ⊓ centralizer (S : Set G) = ⊥)
    (hcentral : K ≤ centralizer (S : Set G)) : Disjoint D K := by
  exact disjoint_iff.mpr (le_antisymm
    ((inf_le_inf_left D hcentral).trans hfaithful.le) bot_le)

end Theory.GroupTheory

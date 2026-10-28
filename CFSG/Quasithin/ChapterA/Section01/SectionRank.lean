module
public import Theory.Quasithin.HighRankOddCoreAction.RankBound

/-!
# The section-rank conclusion of A.1.28

A normal odd-prime core of rank greater than two acts as a detector for
involutions. The actual supercritical Frattini representation has odd kernel;
local rank bounds control its involution fixed spaces. The elementary-two
representation theorem bounds the actor rank by three and, at equality,
produces an involution central modulo the odd core.

The ambient formulation retains the given subgroup H ≤ G. The intrinsic
form and its contrapositive are the inputs used by A.2.11 and A.2.12.
Source: Aschbacher–Smith, Lemma A.1.28, printed p.26.
-/

namespace CFSG.Quasithin.ChapterA
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A.1.28 with the original group used as its own ambient group. -/
public theorem lemma_A_1_28_group
    (hp : Odd p) (hlocal : twoLocalPrimeRank p G ≤ 2)
    (hcore : 2 < primeRank p (pCore p G)) :
    primeRank 2 G ≤ 3 ∧
      (primeRank 2 G = 3 → Subgroup.center (G ⧸ pPrimeCore 2 G) ≠ ⊥) := by
  apply Theory.Quasithin.two_rank_le_three_and_center_oddCore_of_large_normal_p_subgroup
    hp (fun a ha => ?_) (pCore p G) pCore_isPGroup hcore
  exact ((Theory.GroupTheory.isTwoLocal_involution_centralizer ha).primeRank_le p).trans hlocal

/-- A.1.28, including nontrivial Z-star when the subgroup has two-rank three. -/
public theorem lemma_A_1_28
    (hp : Odd p) (hlocal : twoLocalPrimeRank p G ≤ 2)
    (H : Subgroup G) (hcore : 2 < primeRank p (pCore p H)) :
    primeRank 2 H ≤ 3 ∧
      (primeRank 2 H = 3 → Subgroup.center (H ⧸ pPrimeCore 2 H) ≠ ⊥) := by
  exact Theory.Quasithin.two_rank_le_three_and_center_oddCore_of_large_normal_p_subgroup
    hp (Theory.Quasithin.subgroup_involution_centralizer_primeRank_le hlocal H)
    (pCore p H) pCore_isPGroup hcore

/-- The literal core-rank implication used in A.2.11: large two-rank forces
every locally rank-two odd-prime core to have prime rank at most two. -/
public theorem lemma_A_1_28_core_rank_le_two
    (hp : Odd p) (hlocal : twoLocalPrimeRank p G ≤ 2) (hrank : 3 < primeRank 2 G) :
    primeRank p (pCore p G) ≤ 2 := by
  by_contra hn
  exact (not_le_of_gt hrank) (lemma_A_1_28_group hp hlocal (by omega)).1

/-- The equality clause excludes a large odd-prime core when the odd-core
quotient has trivial center, the form used in A.2.12. -/
public theorem lemma_A_1_28_core_rank_le_two_of_center_oddCore_eq_bot
    (hp : Odd p) (hlocal : twoLocalPrimeRank p G ≤ 2) (hrank : 3 ≤ primeRank 2 G)
    (hcenter : Subgroup.center (G ⧸ pPrimeCore 2 G) = ⊥) :
    primeRank p (pCore p G) ≤ 2 := by
  by_contra hn
  obtain ⟨hle, hz⟩ := lemma_A_1_28_group hp hlocal (by omega)
  exact hz (by omega) hcenter
end CFSG.Quasithin.ChapterA

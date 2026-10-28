module

public import Theory.GroupTheory.PerfectSmallTwoAction
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Nontrivial binary modules moved by perfect subgroups

A nonidentity elementary abelian two-subgroup equal to its commutator with a
containing perfect subgroup has rank at least three in the ambient group.
Indeed, rank at most two would give at most four elements, and a perfect
group centralizes every normal subgroup that small.

This is the elementary perfect-action step used in Aschbacher--Smith C.3.1,
printed p.151. The statement retains the actual moved subgroup and actor.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial elementary binary subgroup moved by a containing perfect
subgroup forces ambient two-rank at least three. -/
theorem three_le_primeRank_of_perfect_moved_elementary
    (A U : Subgroup G) [Group.IsPerfect A] [IsElementaryAbelian 2 U]
    (hUA : U ≤ A) (hne : U ≠ ⊥) (hm : U = ⁅U,A⁆) : 3 ≤ primeRank 2 G := by
  by_contra! hr
  have hc : Nat.card U ≤ 4 :=
    (primeRank_le_iff_elementary_card_le G).mp (by omega : primeRank 2 G ≤ 2)
      U inferInstance
  let W := U.subgroupOf A
  let : W.Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_iff_commutator_le_left.mpr hm.ge)
  have hW : Nat.card W ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUA).toEquiv]
    exact hc
  have hz : ⁅W,(⊤ : Subgroup A)⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_of_isPerfect_of_card_le_four _ _ hW)
  have hzero := congrArg (map A.subtype) hz
  rw [map_commutator,map_subgroupOf_eq_of_le hUA,← MonoidHom.range_eq_map,
    range_subtype,Subgroup.map_bot,← hm] at hzero
  exact hne hzero

end Theory.GroupTheory

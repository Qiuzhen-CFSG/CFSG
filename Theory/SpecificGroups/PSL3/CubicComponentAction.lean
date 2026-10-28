module

public import Theory.GroupAction.ComponentRankAction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.SpecificGroups.PSL3.StandardCubicFixedNine.RankBound
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank

/-!
# Cubic actions on binary linear components

The central quotient of the original component supplies its rank-two cubic
subgroup. A central two-kernel preserves this rank. Thus the component action
has kernel prime to three and image of three-rank at most two. The actual
binary automorphism coverage and fixed-nine calculation exclude every cubic
field actor, forcing each order-three normalizer element to act through PGL₃.

The original component, its entire center and its literal normalizer action
are retained. No normality, trivial odd core, action-kernel, standard coverage
or field exclusion is assumed. This is the cubic linear prerequisite of
Aschbacher--Smith A.3.18, pp.51--53, used in 2.5.7 on p.556.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.GroupAction.ComponentRankAction
namespace Matrix.PSL3.CubicComponentAction

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

/-- The original component has three-rank at least two, even with central two-kernel. -/
theorem component_rank {L : Subgroup H} (hZ : IsPGroup 2 (center L))
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (heven : Even n)
    (e : L ⧸ center L ≃* PSL(3,F)) : 2 ≤ primeRank 3 L := by
  have hz : Nat.Coprime 3 (Nat.card (center L)) := by
    obtain ⟨m, hm⟩ := hZ.exists_card_eq
    rw [hm]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  have hr := (Theory.SpecificGroups.SignedThreeCubicRank.linear_projective hF heven)
  rw [← primeRank_congr 3 e] at hr
  exact hr.trans (primeRank_quotient_le_of_coprime 3 (center L) hz)

/-- Every cubic element of the actual component normalizer acts inner-diagonally
on the same central quotient model. -/
theorem cubic_innerDiagonal {L : Subgroup H} (hL : IsComponent H L)
    (hZ : IsPGroup 2 (center L)) (hrank : primeRank 3 H ≤ 2)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (heven : Even n)
    (e : L ⧸ center L ≃* PSL(3,F))
    (x : normalizer (L : Set H)) (hx : x ^ 3 = 1) :
    action L e x ∈ OuterSolvable.innerDiagonal F := by
  let := hL.2
  let : IsSimpleGroup PSL(3,F) := e.isSimpleGroup_congr.mp IsQuasisimple.simple
  let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom.comp (QuotientGroup.mk' (center L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective (center L)))
  have hz : Nat.Coprime 3 (Nat.card (center L)) := by
    obtain ⟨m, hm⟩ := hZ.exists_card_eq
    rw [hm]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  by_cases ha : action L e x = 1
  · rw [ha]
    exact (OuterSolvable.innerDiagonal F).one_mem
  have ha3 : orderOf (action L e x) = 3 := orderOf_eq_prime
    (by rw [← map_pow, hx, map_one]) ha
  apply StandardCubicFixedNine.innerDiagonal_of_primeRank_three_le_two
    (Group.IsPerfect.not_isSolvable PSL(3,F)) hF heven (action L e).range
    (inner_le_range L e)
    (range_rank_le_two L e hz (component_rank hZ hF heven e) hrank)
    (action L e x) ⟨x, rfl⟩ _ ha3
  rw [OuterSolvable.standard_eq_top_of_two_power_card F hn hF]
  trivial

/-- The closure of the actual cubic normalizer elements has only inner-diagonal
image. This is the theta-image assertion, before the extension is identified. -/
theorem cubic_closure_image_le {L : Subgroup H} (hL : IsComponent H L)
    (hZ : IsPGroup 2 (center L)) (hrank : primeRank 3 H ≤ 2)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (heven : Even n)
    (e : L ⧸ center L ≃* PSL(3,F)) :
    (closure {x : normalizer (L : Set H) | orderOf x = 3}).map (action L e) ≤
      OuterSolvable.innerDiagonal F := by
  apply map_le_iff_le_comap.mpr
  apply (closure_le _).mpr
  intro x hx
  exact cubic_innerDiagonal hL hZ hrank hn hF heven e x
    (hx ▸ pow_orderOf_eq_one x)

end Matrix.PSL3.CubicComponentAction

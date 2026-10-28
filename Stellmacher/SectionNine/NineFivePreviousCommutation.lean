module
public import Stellmacher.SectionNine.NineEightNeighborhood
public import Stellmacher.SectionNine.NineFivePenultimateJoinAction

/-!
# Earlier-module commutation for Stellmacher (9.5)

For a commuting critical path of length greater than one, the neighbor module
at path offset b−2 centralizes the first-step module. Centers from their two
neighborhoods have distance at most b−1. Critical minimality puts each first
center in the opposite two-core, while (7.3) puts the opposite center in that
core's center; taking both joins proves the assertion.

Consequently the actual intersection of the terminal and earlier modules is
fixed by every prescribed first-step actor. A conjugator in the penultimate
residual two-core fixes both adjacent vertices, so it preserves this same
intersection. These are the geometric inputs for the order-eight intersection
in the distinct-support case of (9.5). No support cardinality is assumed.

Source: Stellmacher, Journal of Algebra 190 (1997), (9.5), printed pp.52–53
of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_five_previous_module_commutes_first
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length)
    (prev : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) prev) :
    ⁅VAt ctx.Γ prev, VAt ctx.Γ ctx.criticalPath.firstStep⁆ = ⊥ := by
  have hthree : 3 ≤ ctx.criticalPath.length := by
    obtain ⟨n, hn⟩ := (lemma_seven_five ctx.sectionSeven ctx.Γ
      ctx.criticalPath ctx.commutator_eq).odd_distance
    omega
  obtain ⟨index, hindex, rfl⟩ := hpath
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  rw [VAt, v, ctx.Γ.vAt_def]
  apply sSup_le
  rintro center ⟨last, hlast, rfl⟩
  apply Subgroup.le_centralizer_iff.mpr
  rw [VAt, v, ctx.Γ.vAt_def]
  apply sSup_le
  rintro center ⟨first, hfirst, rfl⟩
  have hfirstAdj := ctx.Γ.adjacent_symm
    ((mem_neighborhood_iff_adjacent ctx.Γ).mp hfirst)
  have hlastAdj := ctx.Γ.adjacent_symm
    ((mem_neighborhood_iff_adjacent ctx.Γ).mp hlast)
  have hdist := neighbor_path_distance_le ctx.Γ ctx.criticalPath first
    1 (ctx.criticalPath.length - 2) (by omega) (by omega)
    (by simpa only [ctx.criticalPath.path_first] using hfirstAdj)
  have hindexEq : index = ⟨ctx.criticalPath.length - 2, by omega⟩ := Fin.ext hindex
  rw [← hindexEq] at hdist
  have hlastDist := nine_eight_adjacent_distance_le ctx.Γ
    (target := first) hlastAdj
  rw [ctx.Γ.distance_symm last first,
    ctx.Γ.distance_symm (ctx.criticalPath.path index) first] at hlastDist
  have hle := critical_minimality ctx.Γ ctx.criticalPath
    (d := first) (l := last) (by omega)
  have hcenter := (lemma_seven_three ctx.sectionSeven ctx.Γ).center_core
    last (ctx.criticalPath.path index)
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hlastAdj)
  exact hle.trans (Subgroup.le_centralizer_iff.mpr
    (hcenter.trans ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))))

public theorem nine_five_neighbor_intersection_actor_control
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 1 < ctx.criticalPath.length) (prev : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) prev)
    (actor conjugator : G)
    (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hconjugator : conjugator ∈ twoCoreIn (EAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩))) :
    (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ prev : Subgroup G) ≤
      Subgroup.centralizer (Subgroup.zpowers actor : Set G) ∧
    conjugator ∈ Subgroup.normalizer
      (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ prev : Subgroup G) := by
  constructor
  · exact inf_le_right.trans
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (nine_five_previous_module_commutes_first ctx hb prev hpath)).trans
          (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hactor)))
  · let middle := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    have hcore : twoCoreIn (EAt ctx.Γ middle) ≤ QAt ctx.Γ middle := by
      change twoCoreIn (e ctx.Γ middle) ≤ q ctx.Γ middle
      rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def, q, ctx.Γ.twoCoreAt_def,
        residual_core_eq_inter_core]
      exact inf_le_right
    have hprev := ctx.Γ.adjacent_symm
      (nine_five_previous_adjacent_penultimate ctx hb prev hpath)
    have hconjPrev : conjugator ∈ GAt ctx.Γ prev :=
      ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core middle prev
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hprev) default).2.2
          (hcore hconjugator)
    have hconjTerminal := nine_five_penultimate_core_le_terminal ctx hconjugator
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨stabilizer_le_normalizer_v ctx.Γ _ hconjTerminal,
        stabilizer_le_normalizer_v ctx.Γ _ hconjPrev⟩

end Stellmacher.SectionNine

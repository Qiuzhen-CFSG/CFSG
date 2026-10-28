module
public import CFSG.Quasithin.Defs
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.GroupAction.ComponentRankAction.OuterTwo
public import Theory.SpecificGroups.PSL3Three.RankLower
public import Theory.SpecificGroups.PSL3Three.OuterTwo
public import Theory.Mathieu.M11.Properties.RankLower
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.GroupTheory.GeneralizedFitting.ComponentRankNormality
/-!
# The small centerless cubic-rank-two cases of A.3.18

PSL₃(3) and M₁₁ are centerless with cubic rank at least two and two-group
outer automorphism quotient. Their actual ordinary components in an SQTK
group are therefore normal and equal its prime-to-three residual. This
supplies the earlier residual assertion used in source 2.5.15, retaining
the original subgroup and the literal residual convention.
Source: Aschbacher–Smith A.3.18, pp.51–53, and 2.5.15, p.558.
-/
public section
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.SmallComponents
open Subgroup Theory.GroupTheory
theorem small_rank {K : Type*} [Group K] [Finite K]
    (hm : Nonempty (K ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M11)) :
    2 ≤ primeRank 3 K := by
  rcases hm with hm | hm
  all_goals obtain ⟨e⟩ := hm
  · rw [primeRank_equiv 3 e]
    exact Matrix.PSL3Three.primeRank_three_ge_two
  · rw [primeRank_equiv 3 e]
    exact Sporadic.Mathieu.m11_primeRank_three_ge_two

private theorem center_bot_transport {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : center B = ⊥) : center A = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  have hb : e a ∈ center B := ((centerCongr e) ⟨a,ha⟩).property
  have hb1 : e a = 1 := by simpa only [h,mem_bot] using hb
  exact mem_bot.mpr (e.injective (hb1.trans (map_one e).symm))

theorem small_center {K : Type*} [Group K]
    (hm : Nonempty (K ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M11)) :
    center K = ⊥ := by
  rcases hm with hm | hm
  all_goals obtain ⟨e⟩ := hm
  · exact center_bot_transport (e.trans Matrix.PSL3Three.equiv.symm) Matrix.PSL3Three.center_eq_bot
  · exact center_bot_transport e Sporadic.Mathieu.m11_center_eq_bot

theorem small_card {K : Type*} [Group K]
    (hm : Nonempty (K ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M11)) :
    Nat.card K = 5616 ∨ Nat.card K = 7920 := by
  rcases hm with hm | hm
  all_goals obtain ⟨e⟩ := hm
  · exact .inl ((Nat.card_congr e.toEquiv).trans Matrix.PSL3Three.card_PSL)
  · exact .inr ((Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m11_order)


variable {G : Type*} [Group G] [Finite G]
theorem component_eq_cubic_residual
    (hG : IsSQTK KnownSimple.IsKnownSimple G) {K : Subgroup G}
    (hK : IsComponent G K)
    (hm : Nonempty (K ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M11)) :
    K.Normal ∧ K=primeToResidual 3 G := by
  have hc := small_center hm
  have hr := small_rank hm
  have hb := hG.stronglyQuasithin 3 Nat.prime_three (by decide)
  let e : (K ⧸ center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have houter : IsPGroup 2 (MulAut.Outer K) := by
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      exact Matrix.PSL3Three.outer_isTwoGroup.of_equiv (MulAut.outerCongr e).symm
    · obtain ⟨e⟩ := hm
      exact Sporadic.Mathieu.m11_outer_isPGroup_two.of_equiv (MulAut.outerCongr e).symm
  exact ⟨hK.normal_of_centerless_primeRank hc hr hb,
    (Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual_of_outer_twoGroup
      hK (by rw [hc]; simp) hr hb e (by decide) houter).2⟩
end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.SmallComponents

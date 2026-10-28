module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SolvableThompson
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.EqualCoreSourceAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ModelSelection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearThompsonAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.AlternatingThompsonAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComparisonApplicability

/-!
# The general original pair theorem from guarded structural inputs

The equal-core solvable branch has commuting residual actions. For unequal
cores, commuting actions give the same bound; the Heisenberg action handles
the remaining solvable case. In the nonsolvable branch, the genuine earlier
component list leaves actual linear-three or ordinary A6 quotients, whose
full omega-module actions force J(T) normality.

This constructs exactly Nonsolvable.PairAmalgamSource1347 for all applicable
S3 parabolics at the same G,T. The second vertex need not be the marked plane
normalizer. Structural1222At is used only with its original ambient guard;
no universal structural record, selected component, module-model or amalgam
callback is assumed. The restricted plane theorem's additional exclusions
and final ambient recognition remain separate obligations.
Source: Aschbacher--Smith 13.4.7(1), printed pp.899--902, and its use in
13.4.12, printed p.910.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The genuine general-pair conclusion required by the nonsolvable
comparison. All pair clauses are quantified over the original ambient G,T. -/
theorem pairAmalgamSource1347_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    Nonsolvable.PairAmalgamSource1347 T := by
  intro A B
  dsimp only
  intro hA hB eA eB hne _hchief hiA hiB hcentral
  by_cases hs : Group.IsSolvable (A ⊔ B : Subgroup G)
  · by_cases he : A.pCoreIn 2 = B.pCoreIn 2
    · exact Or.inl (original_pair_equal_core_solvable_at h structural D m
        hA.2 hB.2 eA.some eB.some hne hindexL hiA hiB hcentral h₀ hs he).2.1
    · by_cases hc : ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
          centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G)
      · exact Or.inl (original_pair_commuting_action h₀ D m hA.2 hB.2
          eA.some eB.some hne hiA hiB hcentral hc).2.2.2.1
      · exact Or.inr (original_pair_solvable_thompson_normal h₀ D m hA.2 hB.2
          eA.some eB.some hne hiA hiB hcentral he hs hc)
  · have ho := original_pair_outside h.toHypothesis1221 D m hA.2 hB.2 eA.some eB.some
      hne hindexL hiA hiB hcentral
    obtain ⟨K,hK⟩ := exists_isCComponent_of_not_isSolvable hs
    have hmodels := original_pair_component_models h₀ D m h1332 fixed covered
      hA.2 hB.2 eA.some eB.some hne hiA hiB (hcentral ho.1).2.2 h13316 K hK
    apply Or.inr
    rcases hmodels with hlinear | halternating
    · exact original_pair_linear_thompson_normal_at h₀ h structural D m
        hA.2 hB.2 eA.some eB.some hne ho.2 hindexL hiA hiB
        (hcentral ho.1).2.2 h1332 K hK hlinear.some
    · exact original_pair_alternating_thompson_normal_at h₀ h structural D m
        hA.2 hB.2 eA.some eB.some hne ho.2 hindexL hiA hiB
        (hcentral ho.1).2.2 h1332 K hK halternating.some

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam

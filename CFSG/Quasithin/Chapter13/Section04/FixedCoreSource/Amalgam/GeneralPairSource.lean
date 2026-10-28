module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SolvableThompson
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.EqualCoreSource
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ApplicableNonsolvable
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComparisonApplicability

/-!
# The general-pair consequence of the original amalgam theorem

For every applicable pair of actual S₃ parabolics, commuting residual
actions lift to both residual two-core bounds. Equal vertex cores in the
solvable branch give that same alternative. Otherwise the actual
Heisenberg action quotient forces J(T) normality. The previously completed
nonsolvable branch also normalizes J(T).

This constructs the exact general-pair interface used by the two-weight
comparison, without assuming that the second vertex is the marked plane
normalizer. It retains the original Chapter 12 and 13.3 source inputs.
It does not assert the complete four model alternatives or the separate
plane exclusion of case (iii).

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
theorem pairAmalgamSource1347
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    · exact Or.inl (original_pair_equal_core_solvable h structural D m
        hA.2 hB.2 eA.some eB.some hne hindexL hiA hiB hcentral h₀ hs he).2.1
    · by_cases hc : ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
          centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G)
      · exact Or.inl (original_pair_commuting_action h₀ D m hA.2 hB.2
          eA.some eB.some hne hiA hiB hcentral hc).2.2.2.1
      · exact Or.inr (original_pair_solvable_thompson_normal h₀ D m hA.2 hB.2
          eA.some eB.some hne hiA hiB hcentral he hs hc)
  · exact Or.inr (original_pair_nonsolvable_source h₀ D m h1332 fixed covered
      hA.2 hB.2 eA.some eB.some hne hiA hiB hcentral h13316
      h structural hindexL hs).2

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam

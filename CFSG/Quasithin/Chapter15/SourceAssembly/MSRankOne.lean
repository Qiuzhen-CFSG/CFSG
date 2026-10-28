module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalExclusions
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.MSAssembly

/-!
# Theorem E with the MS rank-one source supplied

The rank-one characteristic-two exclusion requires only the earlier small
MS classifications. Apply it to each original residual choice, preserving
the same local groups, Sylow subgroup and orthogonal action. The complete
15.3.25 callback is thereby discharged without an FF-classification premise.
The separate 15.1.3 and rank-two 15.3.13 source branches remain explicit.

Source: Aschbacher–Smith C.1.32/C.1.34, 15.3.25–32,
and the final proof of Theorem E, printed pp.1130–1134 and 1165.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15
open Section03 ChapterA.Section05To06
open CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The final E application with 15.3.25 discharged by the earlier
classifications for every original residual choice. -/
theorem source_theoremE_of_MS_rank_one
    (earlier : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (h1513 : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      ClassificationModels.IsTheoremEModel G ∨
        ∃ M : Subgroup G, IsOrderingMaximal T M ∧
          Nonempty (NaturalOrthogonalAction M (localModule T M)))
    (h13 : ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theoremE_of_original_exclusions hG T hmany hempty h1513 h13
  intro d hd hM hu Yplus hchoice hshadow
  let d' : CharacteristicTwo.LocalData G := { d with Yplus := Yplus, choice := hchoice }
  have he : MainForward.faithfulLocalComponents d.T = ∅ := hd ▸ hempty
  have hn : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard := hd ▸ hmany
  exact CharacteristicTwo.SourceRankOne.OriginalSource.source_lemma_15_3_25_of_MS_classifications
    earlier hG d' he hM hu hn hshadow

end CFSG.Quasithin.Chapter15

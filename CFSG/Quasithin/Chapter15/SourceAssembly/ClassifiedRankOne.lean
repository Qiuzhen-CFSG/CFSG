module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalExclusions
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.ClassifiedAssembly

/-!
# Theorem E after the classified rank-one exclusion

The classified 15.3.25 theorem excludes characteristic two for each original
choice of the residual subgroup `Yplus`.  Updating that choice in the literal
local datum preserves its Sylow subgroup, orthogonal action and local groups,
so the theorem supplies the entire rank-one callback of the final Theorem E
assembly.  The remaining source branches are 15.1.3 and 15.3.13; the genuine
C.1.32/C.1.34 and B.5 classifications remain explicit earlier inputs.

Source: Aschbacher–Smith, C.1.30–34, 15.3.25–32, and the final proof of
Theorem E, printed pp.1130–1134 and 1165.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15
open Section03 ChapterA.Section05To06
open CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The final E application with 15.3.25 discharged by the earlier
classifications for every original residual choice. -/
theorem source_theoremE_of_classified_rank_one
    (earlier : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (ff : ProjectiveLine.CompleteClassificationInput.{u,u} KnownSimple.IsKnownSimple)
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
  exact CharacteristicTwo.SourceRankOne.OriginalSource.source_lemma_15_3_25_of_classifications
    earlier ff hG d' he hM hu hn hshadow

end CFSG.Quasithin.Chapter15

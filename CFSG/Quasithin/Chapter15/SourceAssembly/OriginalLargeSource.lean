module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalLargeDistanceFour
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.Exclusion

/-!
# Original Theorem E assembly with natural distance four discharged

The original natural A₆ distance-four exclusion now supplies the geometric
input to the original-Sylow assembly. The remaining inputs are the original
rank-two resolver, normalization and subsequent exclusion of the three large
actions at the actual singleton centralizer, and original 15.3.13.

This conditional assembly retains those source obligations.
Source: Aschbacher--Smith 15.1.3, 15.1.14--15, 15.3.13 and Theorem E,
printed pp.1086,1091--1092,1125--1126,1165; MS93 (5.12), pp.924--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original Sylow A₆ pair reconstructs its whole intrinsic core.
Both quotient-center branches are now supplied by source proofs. -/
theorem original_sylow_A6_reconstruction_knownSimple
    {L R : Subgroup G} (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (hSyl : Chapter1.IsSylowIn 2 R (L ⊔ R))
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) :
    AlternatingSixReconstruction L := by
  exact original_sylow_A6_reconstruction_of_distanceFour
    AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.distanceFourInput_knownSimple
    h hSyl e

/-- Theorem E from the remaining original source duties, with the natural
distance-four input proved and all Section 15.1 duties restricted to the
actual singleton centralizer. -/
theorem source_theoremE_of_original_large_sources
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hrank : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      RankTwoResolver T Mc)
    (hnormalize : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      OriginalLargeFullNormalizationAt T Mc)
    (hlarge : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      SourceLargeChosenExclusionInput hG T Mc)
    (h13 : ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) :
    ClassificationModels.IsTheoremEModel G := by
  exact source_theoremE_of_original_large_normalization_distanceFour
    hG T hmany hempty hrank hnormalize hlarge
    AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.distanceFourInput_knownSimple
    h13

end CFSG.Quasithin.Chapter15

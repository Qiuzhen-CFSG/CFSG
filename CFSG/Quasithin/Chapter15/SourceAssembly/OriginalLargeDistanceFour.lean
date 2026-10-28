module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalSylowDistanceFour
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionFifteenConsumer

/-!
# The original Theorem E assembly after the marked-five exclusion

The full marked-five action is excluded independently of the global Thompson
residual assertion. Consequently original 15.1.3 needs normalization only
for the three remaining large actions, together with their subsequent
exclusion and the original rank-two resolver. Apply this source reduction at
each actual singleton centralizer, then use the original-Sylow Theorem E
assembly. The natural A₆ distance-four and original 15.3.13 duties remain.

This is a conditional source assembly. It proves neither the remaining
large-action duties nor Theorem E from the ambient hypotheses alone.
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

/-- The remaining full-module normalization duty, restricted to the three
literal large actions. The original factor-four and strict Thompson-image
guards are retained, as are the global model and natural-action exits. -/
abbrev OriginalLargeFullNormalizationAt (T : Sylow 2 G) (Mc : Subgroup G) : Prop :=
  ¬ ClassificationModels.IsTheoremEModel G →
    (∀ N : Subgroup G, IsOrderingMaximal T N →
      ¬ Nonempty (NaturalOrthogonalAction N (localModule T N))) →
    ∀ (M : Subgroup G) (_hM : IsOrderingMaximal T M), M ≠ Mc →
      elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) →
      ∀ hp : PreparedChosenModule T M (localModule T M),
        letI := hp.elementary
        let V := localModule T M
        let D := internalActionImage M V hp.normalized
        let S := ((T : Subgroup G).subgroupOf M).map
          (actionHom M V hp.normalized).rangeRestrict
        4 ∣ Nat.card D →
        ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M V hp.normalized).rangeRestrict < S →
        LargeChosenAction T M V hp.normalized →
        centralizer (centralInvolutions T : Set G) ≤
          normalizer (thompsonFixed T V : Set G)

/-- Theorem E from the remaining original source duties. Every Section 15.1
input is required only at the actual singleton centralizer. The small-action,
proper-support and full marked-five cases are supplied by checked proofs. -/
theorem source_theoremE_of_original_large_normalization_distanceFour
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
    (hfour : AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFourInput.{u}
      KnownSimple.IsKnownSimple)
    (h13 : ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theoremE_of_original_sylow_distanceFour hG T hmany hempty ?_ hfour h13
  intro Mc hu
  exact source_lemma_15_1_3_of_large_full_normalization hG T hempty hu hmany
    (hrank Mc hu) (hnormalize Mc hu) (hlarge Mc hu)

end CFSG.Quasithin.Chapter15

module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalExclusions
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryOriginalAssembly

/-!
# Theorem E after the original binary rank-one exclusion

For each original residual choice, the first-plane displacement argument
excludes the binary component. The remaining rank-one input is C.1.32 at
the literal small MS pair. The original 15.1.3 and rank-two 15.3.13 inputs
remain explicit and independent; no C.1.34 or whole-fixed-factor premise is
used in this consumer.

Source: Aschbacher--Smith 15.3.25--32 and the proof of Theorem E,
printed pp.1130--1134 and 1165.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15
open Section03 ChapterA.Section05To06
open CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Final E application of the original binary exclusion, with C.1.32
only at the actual pair and the independent earlier source branches explicit. -/
theorem source_theoremE_of_rankTwo_rank_one
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (h1513 : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      ClassificationModels.IsTheoremEModel G ∨
        ∃ M : Subgroup G, IsOrderingMaximal T M ∧
          Nonempty (NaturalOrthogonalAction M (localModule T M)))
    (rankTwo : ∀ (L R : Subgroup G),
      SmallMSPair KnownSimple.IsKnownSimple L R → RankTwoAlternatives L R)
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
  have he : MainForward.faithfulLocalComponents d'.T = ∅ := hd ▸ hempty
  have hn : 1 < (maximalTwoLocalOvergroups (d'.T : Subgroup G)).ncard := hd ▸ hmany
  apply CharacteristicTwo.SourceRankOne.OriginalSource.source_lemma_15_3_25_of_rankTwo_source
    hG d' he hM hu hn hshadow
  intro I c s hm
  exact rankTwo c.L d'.S
    (CharacteristicTwo.SourceRankOne.OriginalSource.source_smallMSPair s hm)

end CFSG.Quasithin.Chapter15

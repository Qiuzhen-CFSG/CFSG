module
public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalExclusions
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeLargeDistance
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryFourSmallDisplacement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.SourceReduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.ReplacementAssembly

/-!
# Theorem E with prescribed replacement and an ambient binary exclusion

The original subgroup induction reduces rank two to component degrees three
and four. The large-distance callback below retains all ambient data through
the fixed Sylow T and its original orthogonal rechoices. Nonabelianity supplies
CommonFacts, and prescribed critical-path replacement supplies Earlier for
that same literal LS input. Degree four uses its proved small-displacement
argument, and degree five uses the original subgroup induction.

At rank one, C.1.32 is used only on the actual SmallMSPair constructed from
the source data. Together with the same prescribed replacement input this
supplies original 15.3.25. The existing final source assembly then applies.

This is a conditional assembly, not a proof of Theorem E: original 15.1.3,
the small C.1.32 classification, prescribed replacement, and the ambient
degree-three contradiction remain explicit. In particular it assumes no
fixation of the source four by the original larger two-core and no universal
C.1.34 classification.

Source: Aschbacher–Smith 15.3.13, 15.3.23–25 and Theorem E, printed
pp.1125,1128–1131,1165; Meierfrankenfeld–Stellmacher (1993), (4.4)–(4.5).
-/

noncomputable section
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15
open Section03 ChapterA.Section05To06
open CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC BinaryMS.MS93 BinaryMS.MS93.DistanceEight.PathCentrality
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Final E assembly with the degree-three ambient branch still explicit.
The two earlier classification/path inputs are applied to their literal source pairs. -/
theorem source_theoremE_of_replacement_and_binary_three
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
    (replacement : ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J)
      (b : BinaryMS.Input KnownSimple.IsKnownSimple L R) (t : InputSetup b),
      CommonFacts t.reduction.radical t.source t.geometry →
      4 < t.geometry.b t.reduction.radical → ∀ {a a'}
      (p : CriticalPath t.reduction.radical t.geometry a a'),
      HasTurnConjugators t.reduction.radical p → PrescribedReplacement t.reduction.radical p)
    (large_three : ∀ (d : CharacteristicTwo.LocalData G), d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc} →
      ∀ (I : Subgroup G), I ∈ d.Hplus → OutsideStructure.RankTwoCase d I →
      CharacteristicTwo.HasCharacteristicTwo I → ∀ (c : CharacteristicTwo.ComponentWitness d I)
      (_e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
      (b : BinaryMS.Input KnownSimple.IsKnownSimple
        (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S))) (t : InputSetup b),
      CommonFacts t.reduction.radical t.source t.geometry →
      DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry →
      ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))) →
      4 < t.geometry.b t.reduction.radical → False) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theoremE_of_original_exclusions hG T hmany hempty h1513
  · intro d hd hM hu Yplus hchoice hrank I hI
    let d' : CharacteristicTwo.LocalData G := { d with Yplus := Yplus, choice := hchoice }
    have he : MainForward.faithfulLocalComponents d'.T = ∅ := hd ▸ hempty
    have hn : 1 < (maximalTwoLocalOvergroups (d'.T : Subgroup G)).ncard := hd ▸ hmany
    have htwo := ComponentIntersection.rank_two_case_of_three_rank_two d' I
      (OutsideStructure.source_lemma_15_3_11_from_selection
        hG d' he hM hu hn I hI).local_structure hrank
    apply CharacteristicTwo.RankTwoElimination.OriginalSource.uniform_exclusion_of_binary_exclusions
      hG d' he hM hu hn hI htwo
      (fun J hJ hj hf c e => ?_) (fun J hJ hj hf c e => ?_) I hI
    · apply CharacteristicTwo.RankTwoElimination.OriginalSource.source_lemma_15_3_23_of_large_distance
        hG d' he hM hu hn hJ hj hf c e
      intro b t hc hb
      obtain ⟨common⟩ := t.commonFacts hc
      exact large_three d' hd hM hu J hJ hj hf c e b t common
        (Source44.SourceEarlier.earlier common hb (replacement _ _ _ b t common hb)) hc hb
    · apply CharacteristicTwo.RankTwoElimination.OriginalSource.source_lemma_15_3_24_four_of_replacement
        hG d' he hM hu hn hJ hj hf c e
      intro h x hx b t common hb
      exact replacement _ _ _ b t common hb
  · intro d hd hM hu Yplus hchoice hshadow
    let d' : CharacteristicTwo.LocalData G := { d with Yplus := Yplus, choice := hchoice }
    have he : MainForward.faithfulLocalComponents d'.T = ∅ := hd ▸ hempty
    have hn : 1 < (maximalTwoLocalOvergroups (d'.T : Subgroup G)).ncard := hd ▸ hmany
    apply CharacteristicTwo.SourceRankOne.OriginalSource.source_lemma_15_3_25_of_rankTwo_and_replacement
      hG d' he hM hu hn hshadow
    · intro I c s hm
      exact rankTwo c.L d'.S (CharacteristicTwo.SourceRankOne.OriginalSource.source_smallMSPair s hm)
    · intro I c s e t common hb
      exact replacement _ _ _ _ t common hb

end CFSG.Quasithin.Chapter15

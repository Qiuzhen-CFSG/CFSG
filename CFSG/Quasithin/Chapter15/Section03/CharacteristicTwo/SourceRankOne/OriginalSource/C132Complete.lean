module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryOriginalAssembly
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.OriginalClassification

/-!
# Original 15.3.25 with C.1.32 supplied

The original source constructs the small MS pair on the literal component
and Sylow subgroup. The completed C.1.32 theorem supplies its full five-way
conclusion, discharging the rank-two input of the original rank-one exclusion.
The original selection and symmetric-three shadow hypotheses are retained.
Source: Aschbacher--Smith C.1.32 and 15.3.25--32, pp.135--136,1130--1134.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- C.1.32 on the actual original component and its specified radical. -/
theorem source_rankTwo_knownSimple
    {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L) :
    RankTwoAlternatives c.L d.S :=
  (source_smallMSPair s hm).rankTwo_knownSimple

/-- The original rank-one exclusion with its C.1.32 input proved. -/
theorem source_lemma_15_3_25_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S) :
    ∀ I ∈ d.Hplus, generalizedFitting I ≠ pCore 2 I := by
  apply source_lemma_15_3_25_of_rankTwo_source hG d hempty hM hu hmany hshadow
  intro I c s hm
  exact source_rankTwo_knownSimple s hm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource

module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.SourceReduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryFourSmallDisplacement

/-!
# Original 15.3.13 with the degree-four action premise discharged

The minimal-subgroup induction leaves binary component degrees three and
four. The degree-four residual is now excluded by small displacement in its
canonical point line, so it retains prescribed replacement alone. Degree
three retains its separate original-two-core action obligation.

This specialized route preserves the existing general classification and
geometric interfaces. Both remaining hypotheses refer to the actual original
source inputs; no classified whole-core shape is inserted as a premise.

Source: Aschbacher–Smith 15.3.13 and 15.3.23–24, printed pp.1125–1130.
-/

public section
open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open ChapterC ChapterC.BinaryMS ChapterC.BinaryMS.MS93
open ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open LinearFourFive NaturalDualParabolic NaturalDualParabolic.Realization
variable {G : Type*} [Group G] [Finite G]

/-- The rank-two source induction needs original-core action only in degree three. -/
theorem uniform_exclusion_of_binary_geometry_and_four_replacement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (three_geometry : ∀ (J : Subgroup G), J ∈ d.Hplus →
      OutsideStructure.RankTwoCase d J → HasCharacteristicTwo J →
      ∀ (c : ComponentWitness d J), ((c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2)) →
      ∀ (b : Input KnownSimple.IsKnownSimple
        (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
        (t : InputSetup b), CommonFacts t.reduction.radical t.source t.geometry →
        ¬ IsMulCommutative (commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))) →
        4 < t.geometry.b t.reduction.radical →
        (∀ {a a'} (p : CriticalPath t.reduction.radical t.geometry a a'),
          HasTurnConjugators t.reduction.radical p → PrescribedReplacement t.reduction.radical p) ∧
        t.reducedCentralFour ≤ centralizer
          (pCore 2 (c.L ⊔ d.S : Subgroup G) : Set (c.L ⊔ d.S : Subgroup G)))
    (four_replacement : ∀ (J : Subgroup G), J ∈ d.Hplus →
      OutsideStructure.RankTwoCase d J → HasCharacteristicTwo J →
      ∀ (c : ComponentWitness d J), ((c.L ⧸ pCore 2 c.L) ≃* PSL(4,ZMod 2)) →
      ∀ (h : NaturalDual d c.L) (x : Space 4), x ≠ 0 →
      ∀ (input : Input KnownSimple.IsKnownSimple (residualComponent h x) (sylowPart h x))
        (t : InputSetup input), CommonFacts t.reduction.radical t.source t.geometry →
        4 < t.geometry.b t.reduction.radical → ∀ {a a'}
        (p : CriticalPath t.reduction.radical t.geometry a a'),
        HasTurnConjugators t.reduction.radical p → PrescribedReplacement t.reduction.radical p) :
    ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J := by
  apply uniform_exclusion_of_binary_exclusions hG d hempty hM hu hmany hI htwo
  · intro J hJ hj hf c e
    exact source_lemma_15_3_23_of_replacement_and_core_action
      hG d hempty hM hu hmany hJ hj hf c e (three_geometry J hJ hj hf c e)
  · intro J hJ hj hf c e
    exact source_lemma_15_3_24_four_of_replacement
      hG d hempty hM hu hmany hJ hj hf c e (four_replacement J hJ hj hf c e)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

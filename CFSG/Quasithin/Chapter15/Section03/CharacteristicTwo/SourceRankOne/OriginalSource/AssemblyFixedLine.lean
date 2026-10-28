module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.Assembly
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.FixedLineComplete
/-!
# Original 15.3.25 after the fixed-line branch

The middle-node branch is discharged by the original fixed-line residual
identity, preserving the marked subgroup and the actual centralizer. Only
the independent small-core and large-distance MS inputs remain explicit.

Source: Aschbacher–Smith 15.3.25 and15.3.32(3), printed pp.1129–1134.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension
variable {G : Type*} [Group G] [Finite G]
/-- Original15.3.25 with its middle-node fixed-line branch proved internally. -/
theorem source_lemma_15_3_25_of_small_core_branches
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    (hA6 : ∀ {I : Subgroup G} (c : ComponentWitness d I),
      SourceData KnownSimple.IsKnownSimple d c →
      Parabolics.RankTwoParabolicMarking d I c.L
        (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) Parabolics.symplecticDerivedParabolic →
      ChapterC.IsBlock (c.L.subgroupOf (c.L ⊔ d.S)) ∧ ChapterC.IsAlternatingBlock c.L 6)
    (hG2 : ∀ {I : Subgroup G} (c : ComponentWitness d I),
      SourceData KnownSimple.IsKnownSimple d c →
      Parabolics.RankTwoParabolicMarking d I c.L
        (commutator (Atlas.G2.Model (ZMod 2))) Parabolics.g2DerivedParabolic →
      ChapterC.IsBlock (c.L.subgroupOf (c.L ⊔ d.S)) ∧ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.IsG2TwoBlock c.L)
    (hlarge : ∀ {I : Subgroup G} (c : ComponentWitness d I)
      (s : SourceData KnownSimple.IsKnownSimple d c)
      (_ : Parabolics.RankTwoParabolicMarking d I c.L SmallExtension.CentralCover.LinearThree.SL
        Parabolics.linearThreeParabolic)
      (e : (c.L ⧸ pCore 2 c.L) ≃* SmallExtension.CentralCover.LinearThree.SL)
      (t : ChapterC.BinaryMS.MS93.InputSetup (source_binaryMSInput s e)),
      ¬ IsMulCommutative (ChapterC.BinaryMS.commutatorCore (c.L.subgroupOf I)) →
      4 < t.geometry.b t.reduction.radical → False) :
    ∀ I ∈ d.Hplus, generalizedFitting I ≠ pCore 2 I := by
  apply source_lemma_15_3_25_of_core_branches hG d hempty hM hu hmany hshadow hA6 hG2 hlarge
  intro I hI hf c mark
  exact source_lemma_15_3_32_3 hG d hempty hM hu hmany hshadow hI hf c mark

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource

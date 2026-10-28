module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.LinearTwo
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.PairedGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.SmallAssembly
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.Inheritance

/-!
# Original rank-one characteristic-two exclusion: branch assembly

Minimalize an outside characteristic-two subgroup, extract its actual
component and apply the source parabolic alternatives. The rank-one linear
row is already impossible. The small rows use their exact core inputs;
the middle row uses its fixed-line residual equality and the proved paired
terminal. All callbacks retain the original subgroup, marking and maps.

This is a conditional assembly of15.3.25. Its remaining inputs are whole-core
reconstruction in the A₆ and G₂ rows, the binary MS large-distance
contradiction, and the fixed-line residual equality of15.3.32(3).

Source: Aschbacher–Smith15.3.25–32, printed pp.1129–1134.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension
variable {G : Type*} [Group G] [Finite G]

/-- Original rank-one source assembly, with only the small MS branch and the
middle-node fixed-line residual identity supplied by their actual source owners. -/
theorem source_not_characteristicTwo_of_branches
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    (hsmall : ∀ {I : Subgroup G} (c : ComponentWitness d I),
      SourceData KnownSimple.IsKnownSimple d c →
      Parabolics.SmallParabolicMarking d I c.L → False)
    (hmiddle : ∀ {I : Subgroup G} (c : ComponentWitness d I),
      EndNodeData d I c → Parabolics.MiddleNodeFlagMarking d I c.L →
      c.L = RankOne.threeResidualIn (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G))) :
    ∀ I ∈ d.Hplus, generalizedFitting I ≠ pCore 2 I := by
  intro I hI hf
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI
  obtain ⟨K,_,hK,hfK⟩ := d.exists_minimal_outside_characteristicTwo hI h11.sylow hf
  obtain ⟨c⟩ := source_lemma_15_3_26_2 hG d hempty hM hu hmany hK.1 hfK
  cases source_lemma_15_3_28 hG d hempty hM hu hmany hshadow hK hfK c with
  | linearTwo F mark =>
    exact source_lemma_15_3_30 hG d hempty hM hu hmany hshadow hK hfK c mark
  | small mark =>
    obtain ⟨s⟩ := source_smallData hG d hempty hM hu hmany hshadow hK hfK c
    exact hsmall c s mark
  | middle mark =>
    obtain ⟨e⟩ := source_endNodeData hG d hempty hM hu hmany hshadow hK hfK c mark
    exact e.false_of_fixedLineResidual (hmiddle c e mark)

/-- The literal source25 assembly with the four genuine remaining branches
exposed at their actual marked components. The paired terminal, local MS
geometry, quotient lift and all small binary cases are internal. -/
theorem source_lemma_15_3_25_of_core_branches
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
      4 < t.geometry.b t.reduction.radical → False)
    (hfixedLine : ∀ {I : Subgroup G} (_hI : I ∈ d.HplusMinimal) (_hf : HasCharacteristicTwo I)
      (c : ComponentWitness d I), Parabolics.MiddleNodeFlagMarking d I c.L →
      c.L = RankOne.threeResidualIn (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G))) :
    ∀ I ∈ d.Hplus, generalizedFitting I ≠ pCore 2 I := by
  apply source_not_characteristicTwo_of_branches hG d hempty hM hu hmany hshadow
  · intro I c s hm
    exact source_small_false_of_core_branches s hm (hA6 c s) (hG2 c s) (hlarge c s)
  · intro I c e mark
    exact hfixedLine e.source.minimal e.source.characteristicTwo c mark

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource

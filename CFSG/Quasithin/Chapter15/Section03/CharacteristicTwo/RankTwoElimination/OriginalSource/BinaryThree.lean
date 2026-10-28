module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.AbelianExclusion
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic

/-!
# Original-input three-dimensional characteristic-two reductions

The original rank-two setup supplies elementarity, Thompson generation, and
radical saturation for the actual component span. These instantiate the
PSL₃(2) source consumer on the literal subgroup LS and its original Sylow S.
The abelian commutator-core branch uses the proved binary MS quotient theorem
and leaves no classification premise; the general branch retains only the
classification of this particular binary MS input.

Source: Aschbacher–Smith 15.3.23, printed pp.1128–1129.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
universe u
variable {G : Type u} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
include hG hempty hM hu hmany hI htwo hf e

/-- Original 15.3.23 with its local geometric premises discharged.
The sole remaining input is C.1.34 on the actual LS binary MS pair. -/
theorem source_lemma_15_3_23_of_binary_ms
    (classification : ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)) →
      ∀ P : Sylow 2 (c.L ⊔ d.S : Subgroup G),
        d.S.subgroupOf (c.L ⊔ d.S) ≤ (P : Subgroup (c.L ⊔ d.S : Subgroup G)) →
        ∃ e' : ((c.L.subgroupOf (c.L ⊔ d.S)) ⧸
          pCore 2 (c.L.subgroupOf (c.L ⊔ d.S))) ≃* Matrix.PSL3Two.SL,
          Alternatives (ZMod 2) 1 (c.L.subgroupOf (c.L ⊔ d.S))
            (d.S.subgroupOf (c.L ⊔ d.S)) P e') : False := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  exact LinearThree.OriginalSource.contradiction_from_selection_of_binary_source
    hG d hempty hM hu hmany hI hf c classification
    (OutsideStructure.rankTwoCase_three_rank hG d hI htwo)
    (e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))) hW hJ hcore

/-- The abelian intrinsic commutator core is excluded from original inputs,
using the proved binary MS quotient classification. -/
theorem source_lemma_15_3_23_of_abelian_core
    (hc : IsMulCommutative (sourceQ (c.L.subgroupOf (c.L ⊔ d.S)))) : False := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  exact LinearThree.OriginalSource.contradiction_from_selection_of_abelian_core
    hG d hempty hM hu hmany hI hf c
    (OutsideStructure.rankTwoCase_three_rank hG d hI htwo)
    (e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))) hW hJ hcore hc

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

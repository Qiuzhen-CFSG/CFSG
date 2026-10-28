module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.CharacteristicTwo.Contracts
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Preparation
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.CommutationSource
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.Generation
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex.NormalBlockRank
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.SylowMaximal

/-!
# The literal L₃ block selection in the characteristic-two case

This is the same-G,T version of the corresponding CentralizerBound proof.
Its configuration carries only Structural1222At at the original Sylow;
every subgroup, action and relative component map is unchanged.

The relative C.1.9 commutation input is applied inside each actual
characteristic-two overgroup. The resulting E.6.7 decomposition has one block
because the marked action on the escaping hyperplane is faithful. A rank-one
block over a larger field would have module rank at least two and therefore
cannot fit in the actual hyperplane of corank one. The surviving block is
therefore an alternating-three or alternating-five block.

Source: Aschbacher–Smith E.6.7 and E.6.14, printed pp.246–251; the
rank-one corank calculation is the first case of 12.4.8, printed p.815.
-/

public section
open CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.CharacteristicTwo
open ChapterE.Section06 ChapterE.Section06.InvariantSubspaces
open ChapterE.Section06.InvariantSubspaces.BlockSelection
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- Retain the original Thompson movement equation for the C.5.4 constructors. -/
theorem blockSelection_moved (c : Configuration T L V U)
    (hc : HasCharacteristicTwo (centralizer (U : Set G)))
    (ha : HasFaithfulThreeAction U) :
    ∃ J : Subgroup G, SingleBlock T (normalizer (V : Set G)) V U J ∧
      (ChapterC.IsAlternatingBlock J 3 ∨ ChapterC.IsAlternatingBlock J 5) ∧
      J = ⁅J, Stellmacher.elementaryAbelianMaxJ (sylowCentralizer (T : Subgroup G) V)⁆ := by
  have hE := source_hypothesisE61 c.hypothesis c.structural c.extension c.fixed_nontrivial
  have hU := (escaping_subspaces c.hypothesis c.structural c.extension
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape).2.2.2.1
  have hSyl := hE.sylow_obstruction hU
  have hQH := (Chapter1.isSylowIn_iff.mp hSyl).2.1
  obtain ⟨d⟩ := e67Input_knownSimple hE U hU (centralizer (U : Set G)) hQH le_rfl hc
  have hcount := d.toBlockFamily.count_eq_one_of_faithful_three hE hU hc fixedNineInput ha
  let i : Fin d.count := ⟨0, by omega⟩
  have hi := faithfulIndexInput_of_commutation_and_quotient_rank
    conjugateChiZeroCommutationInput normalChiZeroQuotientRankInput hE U hU hc ha d hcount i
  have hr := chiZero_eq_primeToResidual_of_index (d.le i) (d.type i) (d.subnormal i) hi
  have hn : ((d.block i).subgroupOf (centralizer (U : Set G))).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    rw [hr]
    exact (centralizer (U : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (centralizer (U : Set G))
        (primeToResidual 3 (centralizer (U : Set G))))
  refine ⟨d.block i, ⟨d.le i, d.toBlockFamily.generated_of_count_eq_one hcount i,
    d.type i, hr, blockSylowMaximalInput _ _ _ hc hSyl (d.le i) hn (d.type i)⟩,
    ?_, d.thompson i⟩
  rcases d.type i with ⟨n, hn⟩ | hAlt
  · obtain ⟨X, _, _, _, _, _, _, _, _, hbound⟩ := d.rankOne i n hn
    have hge := hn.1
    rw [c.corank] at hbound
    omega
  · exact hAlt

/-- The E.6.14 block-selection contract for the original hyperplane. -/
theorem blockSelection (c : Configuration T L V U) : BlockSelection c := by
  intro hc ha
  obtain ⟨J,hJ,ht,_⟩ := blockSelection_moved c hc ha
  exact ⟨J,hJ,ht⟩

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.CharacteristicTwo
end

module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryMarking
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction

/-!
# The original binary small-component branch

The star marking lifts to the intrinsic component quotient. Abelian cores
and nonabelian distance-four cores are excluded by their actual marked
module actions. The even-distance theorem then leaves precisely the
large-distance contradiction at the same original MS pair.

Source: Aschbacher–Smith15.3.31, printed p.1132; C.1.34 and MS93§3–4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.CentralCover
  SmallExtension.CentralCover.LinearThree ChapterC
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

omit [Finite G] in
private theorem binaryCore_map (s : SourceData KnownSimple.IsKnownSimple d c) :
    (BinaryMS.commutatorCore (c.L.subgroupOf I)).map I.subtype = extensionCore c.L := by
  change (⁅pCore 2 I,c.L.subgroupOf I⁆).map I.subtype = _
  rw [map_commutator,map_subgroupOf_eq_of_le (component_le c)]
  change ⁅I.pCoreIn 2,c.L⁆ = extensionCore c.L
  rw [extensionCore_eq_overgroup d c s.contains s.normal]

/-- The original binary row reduces only to its genuine large-distance
contradiction: the abelian and distance-four cases are already discharged. -/
theorem source_linearThree_false_of_large_distance
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (m : Parabolics.RankTwoParabolicMarking d I c.L SL Parabolics.linearThreeParabolic)
    (hlarge : ∀ (e : (c.L ⧸ pCore 2 c.L) ≃* SL)
      (t : BinaryMS.MS93.InputSetup (source_binaryMSInput s e)),
      ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf I)) →
      4 < t.geometry.b t.reduction.radical → False) : False := by
  obtain ⟨e,he⟩ := source_binary_quotient_marking s m
  let b := source_binaryMSInput s e
  by_cases hc : IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf I))
  · have hQ : IsMulCommutative (extensionCore c.L) := by
      rw [← binaryCore_map s]
      let := hc
      infer_instance
    exact source_binary_abelian_false s (.linearThree m) e hQ
  · obtain ⟨t⟩ := BinaryMS.MS93.exists_setup b hc
    obtain ⟨common⟩ := t.commonFacts hc
    have hfour := source_binary_nonabelian_distance_ne_four s (.linearThree m) e t hc
    have heven := t.geometry.even (BinaryMS.MS93.alpha t.reduction.radical) rfl
    change Even (t.geometry.b t.reduction.radical) at heven
    obtain ⟨n,hn⟩ := heven
    exact hlarge e t hc (by have := common.large_distance; omega)

/-- The literal original hypotheses feed the remaining large-distance source
branch after the full quotient marking is constructed internally. -/
theorem source_lemma_15_3_31_linearThree_of_large_distance
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I)
    (m : Parabolics.RankTwoParabolicMarking d I c.L SL Parabolics.linearThreeParabolic)
    (hlarge : ∀ (s : SourceData KnownSimple.IsKnownSimple d c)
      (e : (c.L ⧸ pCore 2 c.L) ≃* SL)
      (t : BinaryMS.MS93.InputSetup (source_binaryMSInput s e)),
      ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf I)) →
      4 < t.geometry.b t.reduction.radical → False) : False := by
  obtain ⟨s⟩ := source_smallData hG d hempty hM hu hmany hshadow hI hf c
  exact source_linearThree_false_of_large_distance s m (hlarge s)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource

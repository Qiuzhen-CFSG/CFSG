module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryAbelian
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.SourceSetup.BinaryFullCover
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.FullCoreCover.Transport

/-!
# The original nonabelian binary distance-four exclusion

The actual source supplies a binary MS input in the literal outside group.
For its nonabelian distance-four setup, the genuine full-cover producer gives
the center and derived coordinates with the original marking. Transport along
the actual subgroupOf equivalence feeds the original marked-plane contradiction.
No pure-center identification or universal MS classifier is assumed.

Source: Aschbacher--Smith C.1.34(3),15.3.31, printed pp.136--137,1132.
-/
public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open Theory.GroupTheory ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.CentralCover
  SmallExtension.CentralCover.LinearThree ChapterC
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

/-- The actual binary source cannot have the nonabelian distance-four setup. -/
theorem source_binary_nonabelian_distance_ne_four
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* SL)
    (t : BinaryMS.MS93.InputSetup (source_binaryMSInput s e))
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf I))) :
    t.geometry.b t.reduction.radical ≠ 4 := by
  intro hb
  obtain ⟨h⟩ := t.fullCoreDoubleDualCover_of_nonabelian_distance_four hc hb
  let eK : c.L.subgroupOf I ≃* c.L := subgroupOfEquivOfLe (component_le c)
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (c.L ⧸ pCore 2 c.L) := (e.trans Matrix.PSL3Two.equiv).isSimpleGroup
  exact s.binary_fullCover_false hm (h.comap eK.symm)

/-- The actual original hypotheses exclude the genuine full-cover output,
without requiring a pure center or discarding the fixed kernel. -/
theorem source_lemma_15_3_31_binary_fullCover
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hm : Parabolics.SmallParabolicMarking d I c.L)
    (h : BinaryMS.FullCoreDoubleDualCover c.L) : False := by
  obtain ⟨s⟩ := source_smallData hG d hempty hM hu hmany hshadow hI hf c
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (c.L ⧸ pCore 2 c.L) := (h.marking.trans Matrix.PSL3Two.equiv).isSimpleGroup
  exact s.binary_fullCover_false hm h

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource

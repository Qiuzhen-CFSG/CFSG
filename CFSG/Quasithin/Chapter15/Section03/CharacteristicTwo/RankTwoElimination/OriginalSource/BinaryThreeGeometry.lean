module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeLargeDistance
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.SmallSylow

/-!
# The exact remaining geometry in the original degree-three branch

The actual binary MS input lies in LS, with the original S as a full Sylow
subgroup and central omega of order four. The preceding source reduction
eliminates the abelian core and distance four. At larger distance, prescribed
replacement constructs the required earlier path facts, and centralization
by the original two-core makes the included four-group central in LS. The
shared small-Sylow obstruction then contradicts the original MS condition.

The two geometric premises retain their literal reduced amalgam and original
LS inclusions. Their separate source producers remain responsible for path
replacement and the original two-core action.

Source: Aschbacher–Smith 15.3.23, printed pp.1128–1129; Meierfrankenfeld–
Stellmacher (1993), (4.4)–(4.5.1), printed pp.890–896.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open ChapterA.Section05To06 ChapterC OutsideStructure
open BinaryMS.MS93 BinaryMS.MS93.DistanceEight.PathCentrality
universe u
variable {G : Type u} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
include hG hempty hM hu hmany hI htwo hf e

/-- Original 15.3.23 reduces to prescribed replacement and the action of
O₂(LS) on the actual included four-group. All original local data, small
central omega, common MS facts and smaller-distance exclusions are proved
internally. -/
theorem source_lemma_15_3_23_of_replacement_and_core_action
    (hgeometry : ∀ (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
      (t : InputSetup b) (_common : CommonFacts t.reduction.radical t.source t.geometry),
      ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))) →
      4 < t.geometry.b t.reduction.radical →
      (∀ {a a'} (p : CriticalPath t.reduction.radical t.geometry a a'),
        HasTurnConjugators t.reduction.radical p → PrescribedReplacement t.reduction.radical p) ∧
      t.reducedCentralFour ≤ centralizer
        (pCore 2 (c.L ⊔ d.S : Subgroup G) : Set (c.L ⊔ d.S : Subgroup G))) : False := by
  apply source_lemma_15_3_23_of_small_sylow_large_distance
    hG d hempty hM hu hmany hI htwo hf c e
  intro b P hP hsmall t hc hb
  obtain ⟨common⟩ := t.commonFacts hc
  obtain ⟨replacement,hcore⟩ := hgeometry b t common hc hb
  have hbound : Nat.card (Stellmacher.omegaOneCenterAmbient
      (P : Subgroup (c.L ⊔ d.S : Subgroup G))) ≤ 4 := by
    rw [← hP]
    simpa only [Stellmacher.omegaOneCenterAmbient,
      card_map_of_injective (d.S.subgroupOf (c.L ⊔ d.S)).subtype_injective,
      card_map_of_injective (center (d.S.subgroupOf (c.L ⊔ d.S))).subtype_injective]
      using hsmall
  exact t.false_of_large_distance_of_replacement_and_core_action P hP hbound
    common hb replacement hcore

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

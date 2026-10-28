module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalCoreStructure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightFrattiniPairs

/-!
# The marked characteristic sections of the original binary-three core

The actual original exchange proves the whole fixed-factor equality. Thus
all three marked Frattini sections descend to the original ambient group:
Phi(Q)/Z(Q) is dual natural, C_Q(Phi(Q))/Phi(Q) is doubled dual natural,
and Q/C_Q(Phi(Q)) is doubled natural. One component quotient marking is
used for all three actions. The groups are the literal original Q and its
characteristic subgroups; no point-kernel characteristicity is assumed.

Source: Aschbacher--Smith15.3.23, pp.1128--1129, and MS93(4.5)(v)--(vii),
p.895. These actions do not assert the remaining finite-carrier exclusion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The three actual characteristic sections have one component marking,
with the whole fixed-factor premise discharged by the original exchange. -/
theorem original_core_sections_of_exchange
    (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ e' : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL,
      let Q := commutatorCore L
      let Phi := frattiniIn Q
      let D := Q ⊓ centralizer (Phi : Set G)
      let a := linearThreeActor e'
      let v := Representation.specialLinearNatural (k := ZMod 2) 3
      HasSectionModel L Phi (CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q) a v.dual ∧
        HasSectionModel L D Phi a (v.dual.prod v.dual) ∧
        HasSectionModel L Q D a (v.prod v) := by
  let J := L ⊔ d.S
  let Q := commutatorCore L
  have hQJ : Q ≤ J := (commutatorCore_le L).trans ((map_subtype_le _).trans le_sup_left)
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hfixed := source_fixedFactor_eq_H_of_original_exchange
    d L e h hg b t common earlier g hgT hgS
  have hQ0 : msQ (L.subgroupOf J) (d.S.subgroupOf J) = Q.subgroupOf J := by
    apply map_injective J.subtype_injective
    have hms : msQ (L.subgroupOf J) (d.S.subgroupOf J) =
        BinaryMS.commutatorCore (L.subgroupOf J) := by
      have hp : (⊤ : Subgroup J).pCoreIn 2 = pCore 2 J := pCore_map_iso 2 topEquiv
      rw [msQ,b.sup_eq_top,hp]
    rw [hms,map_subgroupOf_eq_of_le hQJ]
    exact sourceQ_map_subtype (show L ≤ J from le_sup_left) b.component
  have hs := t.frattini_sectionModel_of_fixedFactor common hb hfixed
  obtain ⟨hm,ht⟩ := t.frattini_pairSectionModels_of_fixedFactor common hb hfixed
  change HasSectionModel (L.subgroupOf J)
    (frattiniIn (msQ (L.subgroupOf J) (d.S.subgroupOf J)))
    (CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
      (msQ (L.subgroupOf J) (d.S.subgroupOf J))) _ _ at hs
  rw [hQ0,frattiniIn_subgroupOf hQJ,centerIn_subgroupOf hQJ] at hs
  have hPhiJ : frattiniIn Q ≤ J := (map_subtype_le (frattini Q)).trans hQJ
  have hDc : Q.subgroupOf J ⊓ centralizer ((frattiniIn Q).subgroupOf J : Set J) =
      (Q ⊓ centralizer (frattiniIn Q : Set G)).subgroupOf J := by
    ext x
    constructor
    · rintro ⟨hx,hc⟩
      exact ⟨hx,fun z hz => congrArg Subtype.val (hc ⟨z,hPhiJ hz⟩ hz)⟩
    · rintro ⟨hx,hc⟩
      exact ⟨hx,fun z hz => Subtype.ext (hc z hz)⟩
  change HasSectionModel (L.subgroupOf J)
    (msQ (L.subgroupOf J) (d.S.subgroupOf J) ⊓
      centralizer (frattiniIn (msQ (L.subgroupOf J) (d.S.subgroupOf J)) : Set J))
    (frattiniIn (msQ (L.subgroupOf J) (d.S.subgroupOf J))) _ _ at hm
  change HasSectionModel (L.subgroupOf J)
    (msQ (L.subgroupOf J) (d.S.subgroupOf J))
    (msQ (L.subgroupOf J) (d.S.subgroupOf J) ⊓
      centralizer (frattiniIn (msQ (L.subgroupOf J) (d.S.subgroupOf J)) : Set J)) _ _ at ht
  rw [hQ0,frattiniIn_subgroupOf hQJ,hDc] at hm ht
  let i := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let c := QuotientGroup.congr _ _ i.symm (pCore_map_iso 2 i.symm)
  let em := b.quotientEquiv.trans common.natural.marking
  let e' := c.trans em
  let a := linearThreeActor e'
  have hactor : linearThreeActor em = a.comp i.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change em (QuotientGroup.mk' _ x) = em (c (QuotientGroup.mk' _ (i x)))
    change em (QuotientGroup.mk' _ x) = em (QuotientGroup.mk' _ (i.symm (i x)))
    rw [i.symm_apply_apply]
  rw [hactor] at hs hm ht
  have hDJ : Q ⊓ centralizer (frattiniIn Q : Set G) ≤ J := inf_le_left.trans hQJ
  exact ⟨e',HasSectionModel.of_subgroupOf (J := J) le_sup_left hPhiJ
    ((map_subtype_le (center Q)).trans hQJ) a _ hs,
    HasSectionModel.of_subgroupOf (J := J) le_sup_left hDJ hPhiJ a _ hm,
    HasSectionModel.of_subgroupOf (J := J) le_sup_left hQJ hDJ a _ ht⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full original large-distance source supplies all three literal
characteristic sections with one quotient marking and no added source bound. -/
theorem binary_three_large_distance_original_core_sections
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical) :
    ∃ e' : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL,
      let Q := LinearThree.commutatorCore c.L
      let Phi := frattiniIn Q
      let D := Q ⊓ centralizer (Phi : Set G)
      let a := linearThreeActor e'
      let v := Representation.specialLinearNatural (k := ZMod 2) 3
      HasSectionModel c.L Phi (CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q) a v.dual ∧
        HasSectionModel c.L D Phi a (v.dual.prod v.dual) ∧
        HasSectionModel c.L Q D a (v.prod v) := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨common⟩ := t.commonFacts hc
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hnot : ¬ (d.T : Subgroup G) ≤ d.S := by
    intro hTS
    have ht : d.S.subgroupOf (d.T : Subgroup G) = ⊤ := top_unique (fun x _ => hTS x.property)
    rw [ht,index_top] at hi
    omega
  obtain ⟨g,hgT,hgS⟩ := SetLike.not_le_iff_exists.mp hnot
  exact original_core_sections_of_exchange d c.L eSL h hg b t common hb g hgT hgS

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

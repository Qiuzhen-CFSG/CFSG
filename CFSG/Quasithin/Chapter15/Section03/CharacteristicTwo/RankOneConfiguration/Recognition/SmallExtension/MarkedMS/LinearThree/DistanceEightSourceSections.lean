module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.Input
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightCenter

/-!
# The center and all four distance-eight sections on the original MS pair

The natural summand is the literal [Z(Q),L], and the fixed summand is C_Q(L).
The center decomposition and all four sections use one CommonFacts marking.
The whole fixed-factor equality remains explicit with its existing producer,
qt-ms93-distance-eight-fixed-factor. Original-group centrality and the
radical-centralizer inequality remain with qt-rank-two-ms93, as does final
C.1.34 and linearThree assembly.

Source: Aschbacher--Smith C.1.34(4), printed pp.136--137;
Meierfrankenfeld--Stellmacher (1993), (4.5), printed p.895.
-/

public section
open Subgroup
open CFSG.Quasithin.ChapterC
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
local notation "msCenter" =>
  CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}

/-- The center and all four literal sections in C.1.34(4) share one marking. -/
theorem SmallMSPair.distance_eight_source_sections (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : ¬ IsMulCommutative (msQ L R))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (hfixed : BinaryMS.MS93.core t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical) ⊓
      centralizer (BinaryMS.MS93.Ltilde t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical) :
        Set (FreeAmalgam t.reduction.radical)) =
        BinaryMS.MS93.H t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical)) :
    ∃ e' : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      let C := msQ L R ⊓ centralizer (L : Set G)
      let Zc := msCenter (msQ L R)
      let Uc := ⁅Zc,L⁆
      let Phi := frattiniIn (msQ L R)
      let D := msQ L R ⊓ centralizer (Phi : Set G)
      let a := linearThreeActor e'
      let v := Representation.specialLinearNatural (k := ZMod 2) 3
      IsElementaryAbelian 2 C ∧ Nat.card C = 4 ∧ Zc = C ⊔ Uc ∧ C ⊓ Uc = ⊥ ∧
        HasSectionModel L Uc ⊥ a v ∧
        HasSectionModel L Phi (msCenter (msQ L R)) a v.dual ∧
        HasSectionModel L D Phi a (v.dual.prod v.dual) ∧
        HasSectionModel L (msQ L R) D a (v.prod v) := by
  have hc' : ¬ IsMulCommutative (BinaryMS.commutatorCore (L.subgroupOf (L ⊔ R))) := by
    intro hh
    apply hc
    apply isMulCommutative_iff.mpr
    intro x y
    apply (binaryCoreEquiv L R).symm.injective
    simpa only [map_mul] using
      isMulCommutative_iff.mp hh ((binaryCoreEquiv L R).symm x)
        ((binaryCoreEquiv L R).symm y)
  obtain ⟨common⟩ := t.commonFacts hc'
  obtain ⟨_,hsplit,hdisj,hU⟩ := t.center_source_sections common hb
  obtain ⟨hCe,hCc⟩ := t.fixed_elementary_card_of_fixedFactor common hb hfixed
  let J := L ⊔ R
  let C := msQ L R ⊓ centralizer (L : Set G)
  let Uc := ⁅msCenter (msQ L R),L⁆
  have hZjoin : msCenter (msQ L R) ≤ J :=
    (map_subtype_le (center (msQ L R))).trans (msQ_le_join L R)
  have hCjoin : C ≤ J := inf_le_left.trans (msQ_le_join L R)
  have hUjoin : Uc ≤ J := (@Subgroup.commutator_le_sup G _ _ _).trans
    (sup_le ((map_subtype_le _).trans (msQ_le_join L R)) le_sup_left)
  have hCsub : msQ (L.subgroupOf J) (R.subgroupOf J) ⊓
      centralizer (L.subgroupOf J : Set J) = C.subgroupOf J := by
    rw [msQ_subgroupOf le_sup_left le_sup_right]
    ext x
    constructor
    · rintro ⟨hx,hc⟩
      exact ⟨hx,fun l hl => congrArg Subtype.val (hc ⟨l,(show L ≤ J from le_sup_left) hl⟩ hl)⟩
    · rintro ⟨hx,hc⟩
      exact ⟨hx,fun l hl => Subtype.ext (hc l hl)⟩
  have hUsub : ⁅msCenter (msQ (L.subgroupOf J) (R.subgroupOf J)),L.subgroupOf J⁆ =
      Uc.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_commutator,msQ_subgroupOf le_sup_left le_sup_right,
      centerIn_subgroupOf (msQ_le_join L R),
      map_subgroupOf_eq_of_le hZjoin,
      map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le hUjoin]
  rw [hCsub] at hCe hCc
  rw [hCsub,hUsub,msQ_subgroupOf le_sup_left le_sup_right,
    centerIn_subgroupOf (msQ_le_join L R)] at hsplit
  rw [hCsub,hUsub] at hdisj
  rw [hUsub] at hU
  have hsplit' := congrArg (map J.subtype) hsplit
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hCjoin,
    map_subgroupOf_eq_of_le hUjoin,
    map_subgroupOf_eq_of_le hZjoin] at hsplit'
  have hdisj' := congrArg (map J.subtype) hdisj
  rw [map_inf _ _ _ J.subtype_injective,map_subgroupOf_eq_of_le hCjoin,
    map_subgroupOf_eq_of_le hUjoin,Subgroup.map_bot] at hdisj'
  have hCe' : IsElementaryAbelian 2 C := by
    let := hCe
    exact IsElementaryAbelian.of_surjective (subgroupOfEquivOfLe hCjoin).toMonoidHom
      (subgroupOfEquivOfLe hCjoin).surjective
  have hCc' : Nat.card C = 4 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hCjoin).toEquiv]
    exact hCc
  have hs := t.frattini_sectionModel_of_fixedFactor common hb hfixed
  change HasSectionModel (L.subgroupOf (L ⊔ R))
    (frattiniIn (msQ (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R))))
    (msCenter (msQ (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R)))) _ _ at hs
  rw [msQ_subgroupOf le_sup_left le_sup_right,
    frattiniIn_subgroupOf (msQ_le_join L R),centerIn_subgroupOf (msQ_le_join L R)] at hs
  obtain ⟨hm,ht⟩ := t.frattini_pairSectionModels_of_fixedFactor common hb hfixed
  have hPhiJ : frattiniIn (msQ L R) ≤ L ⊔ R :=
    (map_subtype_le (frattini (msQ L R))).trans (msQ_le_join L R)
  have hDc : (msQ L R).subgroupOf (L ⊔ R) ⊓
      centralizer ((frattiniIn (msQ L R)).subgroupOf (L ⊔ R) : Set (L ⊔ R : Subgroup G)) =
      (msQ L R ⊓ centralizer (frattiniIn (msQ L R) : Set G)).subgroupOf (L ⊔ R) := by
    ext x
    constructor
    · rintro ⟨hx,hc⟩
      exact ⟨hx,fun z hz => congrArg Subtype.val (hc ⟨z,hPhiJ hz⟩ hz)⟩
    · rintro ⟨hx,hc⟩
      exact ⟨hx,fun z hz => Subtype.ext (hc z hz)⟩
  change HasSectionModel (L.subgroupOf (L ⊔ R))
    (msQ (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R)) ⊓
      centralizer (frattiniIn (msQ (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R))) : Set (L ⊔ R : Subgroup G)))
    (frattiniIn (msQ (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R)))) _ _ at hm
  change HasSectionModel (L.subgroupOf (L ⊔ R))
    (msQ (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R)))
    (msQ (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R)) ⊓
      centralizer (frattiniIn (msQ (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R))) : Set (L ⊔ R : Subgroup G))) _ _ at ht
  rw [msQ_subgroupOf le_sup_left le_sup_right,
    frattiniIn_subgroupOf (msQ_le_join L R),hDc] at hm ht
  let i := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  let c := QuotientGroup.congr _ _ i.symm (pCore_map_iso 2 i.symm)
  let em := (h.binaryInput e).quotientEquiv.trans common.natural.marking
  let e' := c.trans em
  let a := linearThreeActor e'
  have hactor : linearThreeActor em = a.comp i.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change em (QuotientGroup.mk' _ x) = em (c (QuotientGroup.mk' _ (i x)))
    change em (QuotientGroup.mk' _ x) = em (QuotientGroup.mk' _ (i.symm (i x)))
    rw [i.symm_apply_apply]
  rw [hactor] at hs hm ht hU
  have hDjoin : msQ L R ⊓ centralizer (frattiniIn (msQ L R) : Set G) ≤ L ⊔ R :=
    inf_le_left.trans (msQ_le_join L R)
  refine ⟨e',hCe',hCc',hsplit',hdisj',?_,HasSectionModel.of_subgroupOf (J := L ⊔ R) le_sup_left hPhiJ
    ((map_subtype_le (center (msQ L R))).trans (msQ_le_join L R)) a _ hs,
    HasSectionModel.of_subgroupOf (J := L ⊔ R) le_sup_left hDjoin hPhiJ a _ hm,
    HasSectionModel.of_subgroupOf (J := L ⊔ R) le_sup_left (msQ_le_join L R) hDjoin a _ ht⟩
  apply HasSectionModel.of_subgroupOf (J := J) le_sup_left hUjoin bot_le a _
  simpa only [bot_subgroupOf] using hU

/-- Original two-core centralization and the original component action together
supply centrality in the actual join. This does not use replacement centrality. -/
theorem SmallMSPair.fixed_le_center_of_core_centralizes (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hcore : msQ L R ⊓ centralizer (L : Set G) ≤
      centralizer ((L ⊔ R).pCoreIn 2 : Set G)) :
    msQ L R ⊓ centralizer (L : Set G) ≤ msCenter (L ⊔ R) := by
  let J := L ⊔ R
  let C := msQ L R ⊓ centralizer (L : Set G)
  have hgen := congrArg (map J.subtype) (h.binaryInput e).core_sup_component
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,
    ← MonoidHom.range_eq_map,range_subtype] at hgen
  change J.pCoreIn 2 ⊔ L = J at hgen
  have hfix : J ≤ centralizer (C : Set G) := by
    rw [← hgen]
    exact sup_le (le_centralizer_iff.mp hcore) (le_centralizer_iff.mp inf_le_right)
  intro x hx
  refine ⟨⟨x,(inf_le_left.trans (msQ_le_join L R)) hx⟩,mem_center_iff.mpr ?_,rfl⟩
  intro j
  exact Subtype.ext ((hfix j.property x hx).symm)

/-- The literal fourth alternative, with only the whole fixed-factor equality
and the two still-unproved original-action/radical clauses explicit. The full
C.1.34 owner qt-rank-two-ms93 must discharge the last two clauses; the exact
fixed-factor equality has producer qt-ms93-distance-eight-fixed-factor. -/
theorem SmallMSPair.distance_eight_source_of_core_centralizes (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : ¬ IsMulCommutative (msQ L R))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (hfixed : BinaryMS.MS93.core t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical) ⊓
      centralizer (BinaryMS.MS93.Ltilde t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical) :
        Set (FreeAmalgam t.reduction.radical)) =
        BinaryMS.MS93.H t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical))
    (hcore : msQ L R ⊓ centralizer (L : Set G) ≤
      centralizer ((L ⊔ R).pCoreIn 2 : Set G))
    (S : Subgroup G) (hineq : MSNotCentralizerCore L R S) :
    ∃ e', MSModuleAlternatives L R S 1 (ZMod 2) e' := by
  obtain ⟨e',hC,hcard,hsplit,hdisj,hU,hPhi,hD,hQ⟩ :=
    h.distance_eight_source_sections e hc t hb hfixed
  refine ⟨e',Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
  exact ⟨hC,by simpa only [Nat.mul_one, Nat.reducePow] using hcard,h.fixed_le_center_of_core_centralizes e hcore,
    hsplit,hdisj,hU,hPhi,hD,hQ,hineq⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

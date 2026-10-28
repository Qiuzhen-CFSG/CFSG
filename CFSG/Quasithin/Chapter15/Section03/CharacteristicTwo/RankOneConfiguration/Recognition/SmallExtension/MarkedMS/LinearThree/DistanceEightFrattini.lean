module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.Input
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightFrattiniPairs

/-!
# The three original distance-eight Frattini sections

The original-input sections descend through the actual join inclusion to the
literal SmallMSPair. One quotient marking identifies Phi(Q)/Z(Q) with the
dual natural module, C_Q(Phi(Q))/Phi(Q) with two dual copies, and Q/C_Q(Phi(Q))
with two natural copies. No quotient-kernel or action callback remains.

The whole fixed-factor equality remains explicit and is produced by
qt-ms93-distance-eight-fixed-factor. The remaining center/fixed-factor
assembly, original-group centrality and radical-centralizer inequalities
stay with qt-rank-two-ms93; these sections alone are not C.1.34.

Source: Aschbacher--Smith C.1.34(4), printed p.136, from
Meierfrankenfeld--Stellmacher (1993), (4.5)(v)--(vii), printed p.895.
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

/-- All three literal original Frattini sections in C.1.34(4), with one marking.
The exact whole fixed-factor premise remains with its existing producer. -/
theorem SmallMSPair.distance_eight_frattini_sections (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : ¬ IsMulCommutative (msQ L R))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (hfixed : BinaryMS.MS93.core t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical) ⊓
      centralizer (BinaryMS.MS93.Ltilde t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical) :
        Set (FreeAmalgam t.reduction.radical)) =
        BinaryMS.MS93.H t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical)) :
    ∃ e' : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      let Phi := frattiniIn (msQ L R)
      let D := msQ L R ⊓ centralizer (Phi : Set G)
      let a := linearThreeActor e'
      let v := Representation.specialLinearNatural (k := ZMod 2) 3
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
  rw [hactor] at hs hm ht
  have hDjoin : msQ L R ⊓ centralizer (frattiniIn (msQ L R) : Set G) ≤ L ⊔ R :=
    inf_le_left.trans (msQ_le_join L R)
  exact ⟨e',HasSectionModel.of_subgroupOf (J := L ⊔ R) le_sup_left hPhiJ
    ((map_subtype_le (center (msQ L R))).trans (msQ_le_join L R)) a _ hs,
    HasSectionModel.of_subgroupOf (J := L ⊔ R) le_sup_left hDjoin hPhiJ a _ hm,
    HasSectionModel.of_subgroupOf (J := L ⊔ R) le_sup_left (msQ_le_join L R) hDjoin a _ ht⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.MSIndependent
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.LinearThree.DoubledNatural


/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalPlaneCentralizers.MSIndependent`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterC
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
local notation "msCenter" =>
  CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem natural_section_order {K U : Subgroup G}
    (a : K →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (h : HasSectionModel K U ⊥ a
      (Representation.specialLinearNatural (k := ZMod 2) 3)) : Nat.card U = 8 := by
  obtain ⟨_,_,_,hn,e,_⟩ := h
  let := hn
  let b := (QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf U)).trans
    (QuotientGroup.quotientBot (G := U))
  have hc := Nat.card_congr (b.symm.trans e).toEquiv
  change Nat.card U = Nat.card (Fin 3 → ZMod 2) at hc
  norm_num only [Nat.card_fun,Nat.card_zmod,Nat.card_fin] at hc
  exact hc

private theorem no_large_distance_of_moved_sixteen {K R E : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple K R)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (x : G) (hx : x ∈ K) (hcard : Nat.card E = 16)
    (hEZ : E ≤ msCenter (msQ K R)) (hm : ⁅zpowers x,E⁆ = E) : False := by
  let D := K ⊔ R
  let U := ⁅msCenter (msQ K R),K⁆
  have hZjoin : msCenter (msQ K R) ≤ D :=
    (map_subtype_le (center (msQ K R))).trans (msQ_le_join K R)
  have hUjoin : U ≤ D := (@Subgroup.commutator_le_sup G _ _ _).trans
    (sup_le hZjoin le_sup_left)
  have hEjoin : E ≤ D := hEZ.trans hZjoin
  have hEU : E ≤ U := by
    rw [←hm,commutator_comm]
    exact commutator_mono hEZ (zpowers_le.mpr hx)
  have hUsub : ⁅msCenter (msQ (K.subgroupOf D) (R.subgroupOf D)),K.subgroupOf D⁆ =
      U.subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [map_commutator,msQ_subgroupOf le_sup_left le_sup_right,
      centerIn_subgroupOf (msQ_le_join K R),map_subgroupOf_eq_of_le hZjoin,
      map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le hUjoin]
  obtain ⟨_,_,_,hU⟩ := t.center_source_sections common hb
  rw [hUsub] at hU
  have h8 : Nat.card (U.subgroupOf D) = 8 := natural_section_order _ hU
  have h16 : Nat.card (E.subgroupOf D) = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEjoin).toEquiv).trans hcard
  have hle := Nat.card_le_card_of_injective
    (inclusion (show E.subgroupOf D ≤ U.subgroupOf D from comap_mono hEU))
    (inclusion_injective _)
  omega

variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original marked plane supplies the full doubled-natural conclusion
on the literal MS pair, without a universal binary classification premise. -/
theorem Context.component_doubled_natural_without_ms (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (S : Subgroup G) (hS : Chapter1.IsSylowIn 2 S (J ⊔ (L ⊔ T).pCoreIn 2))
    (hQS : (L ⊔ T).pCoreIn 2 ≤ S) :
    ∃ e : Chapter1.XiQuotient J ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      HasSectionModel J (msQ J ((L ⊔ T).pCoreIn 2)) ⊥ (linearThreeActor e)
        ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
          (Representation.specialLinearNatural (k := ZMod 2) 3)) ∧
        MSNotCentralizerCore J ((L ⊔ T).pCoreIn 2) S := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let h := s.component_smallMSPair d J j
  obtain ⟨e⟩ := s.binary_linearThree_core_model d J j
  by_cases hc : IsMulCommutative (msQ J Q)
  · obtain ⟨e',he⟩ := h.abelian_source e hc S hS hQS
    exact ⟨e',s.double_natural_of_ms_alternatives d J j S e' he⟩
  have hc' : ¬ IsMulCommutative
      (BinaryMS.commutatorCore (J.subgroupOf (J ⊔ Q))) := by
    intro hh
    apply hc
    apply isMulCommutative_iff.mpr
    intro x y
    apply (binaryCoreEquiv J Q).symm.injective
    simpa only [map_mul] using isMulCommutative_iff.mp hh
      ((binaryCoreEquiv J Q).symm x) ((binaryCoreEquiv J Q).symm y)
  obtain ⟨t⟩ := BinaryMS.MS93.exists_setup (h.binaryInput e) hc'
  obtain ⟨common⟩ := t.commonFacts hc'
  by_cases hb : t.geometry.b t.reduction.radical = 4
  · obtain ⟨e',he⟩ := h.distance_four_source_complete e hc t hb hS hQS
    exact ⟨e',s.double_natural_of_ms_alternatives d J j S e' he⟩
  have hlarge : 4 < t.geometry.b t.reduction.radical := by
    have he := t.geometry.even (BinaryMS.MS93.alpha t.reduction.radical) rfl
    change Even (t.geometry.b t.reduction.radical) at he
    obtain ⟨n,hn⟩ := he
    have hl := common.large_distance
    omega
  obtain ⟨n,hnJ,hn⟩ := s.component_marked_cubic d J j
  exact (no_large_distance_of_moved_sixteen h e t common hlarge n.val hnJ
    (perpendicular_card d.coordinates) (s.perpendicular_le_msCoreCenter d J j)
    (perpendicular_commutator d.chart d.coordinates d.equivariant n hn)).elim

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers

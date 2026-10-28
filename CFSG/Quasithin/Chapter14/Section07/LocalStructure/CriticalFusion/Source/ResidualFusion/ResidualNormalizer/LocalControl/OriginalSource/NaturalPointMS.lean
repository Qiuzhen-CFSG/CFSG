module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource.ClassificationInput
public import CFSG.Quasithin.ChapterC.Section01.NaturalPointControl.ClassificationExclusions
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.DistanceEightOriginalAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.DistanceFourComplete
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.AbelianSourceComplete

/-!
# The MS conclusion for the original natural-point action

For the actual Baumann MS pair, the abelian and distance-four source theorems
combine with the natural-point exclusions. At larger distance, only the
natural module [Z(Q),L] is needed. The point-radical identity then contradicts
the original radical-centralizer inequality supplied by MS93 movement.
Thus the commutator core is natural or doubled natural without invoking the
universal C.1.34 classifier, the whole fixed-factor equality, or centrality
under the original larger two-core.

The module marking and the Sylow subgroup remain those of the literal
Baumann MS pair. NaturalPointMSApplication applies the conclusion to the
original Rudvalis datum and its independent four-factor chief series.

Source: Aschbacher--Smith C.1.34 and C.1.37, printed pp.136--137,141--143;
Meierfrankenfeld--Stellmacher (1993), (4.4)--(4.6) and Section 7.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.LocalControl.OriginalSource
open Subgroup ChapterC ChapterC.NaturalPointControl
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
local notation "msCenter" =>
  CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
universe u

private theorem distance_eight_center_commutator_section
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
    (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical) :
    ∃ e' : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      HasSectionModel L ⁅msCenter (msQ L R),L⁆ ⊥ (linearThreeActor e')
        (Representation.specialLinearNatural (k := ZMod 2) 3) := by
  obtain ⟨_,_,_,hU⟩ := t.center_source_sections common hb
  let J := L ⊔ R
  let Uc := ⁅msCenter (msQ L R),L⁆
  have hZjoin : msCenter (msQ L R) ≤ J :=
    (map_subtype_le (center (msQ L R))).trans (msQ_le_join L R)
  have hUjoin : Uc ≤ J := (@Subgroup.commutator_le_sup G _ _ _).trans
    (sup_le hZjoin le_sup_left)
  have hUsub : ⁅msCenter (msQ (L.subgroupOf J) (R.subgroupOf J)),L.subgroupOf J⁆ =
      Uc.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_commutator,msQ_subgroupOf le_sup_left le_sup_right,
      centerIn_subgroupOf (msQ_le_join L R),map_subgroupOf_eq_of_le hZjoin,
      map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le hUjoin]
  rw [hUsub] at hU
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
  rw [hactor] at hU
  refine ⟨e',?_⟩
  apply HasSectionModel.of_subgroupOf (J := J) le_sup_left hUjoin bot_le a _
  simpa only [bot_subgroupOf] using hU

variable {X : Type u} [Group X] [Finite X] {V : Subgroup X} [V.Normal]
  [IsElementaryAbelian 2 V] {κ : GroupClass.{u}}

/-- The natural-point MS pair has a natural or doubled-natural whole core.
All source inputs are discharged on the actual pair and original Sylow. -/
theorem natural_or_double_of_msInput (a : NaturalAction V)
    (h : BinaryMS.Input κ a.LJ a.BJ) :
    ∃ e : (a.LJ ⧸ pCore 2 a.LJ) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      HasSectionModel a.LJ (msQ a.LJ a.BJ) ⊥ (linearThreeActor e)
        (Representation.specialLinearNatural (k := ZMod 2) 3) ∨
      HasSectionModel a.LJ (msQ a.LJ a.BJ) ⊥ (linearThreeActor e)
        ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
          (Representation.specialLinearNatural (k := ZMod 2) 3)) := by
  obtain ⟨S,hS⟩ := h.radical.isPGroup.exists_le_sylow
  have hs : Chapter1.IsSylowIn 2 (S : Subgroup a.J) (a.LJ ⊔ a.BJ) := by
    rw [h.sup_eq_top]
    exact Chapter1.isSylowIn_iff.mpr ⟨S.isPGroup',le_top,fun U hu hsu _ => S.is_maximal' hu hsu⟩
  let hm := smallMSPair_of_input h
  let e := h.quotientEquiv
  by_cases hc : IsMulCommutative (msQ a.LJ a.BJ)
  · obtain ⟨e',he⟩ := hm.abelian_source e hc S hs hS
    exact ⟨e',a.ms_natural_or_double h S hS e' he⟩
  have hc' : ¬ IsMulCommutative
      (BinaryMS.commutatorCore (a.LJ.subgroupOf (a.LJ ⊔ a.BJ))) := by
    intro hh
    apply hc
    apply isMulCommutative_iff.mpr
    intro x y
    apply (binaryCoreEquiv a.LJ a.BJ).symm.injective
    simpa only [map_mul] using isMulCommutative_iff.mp hh
      ((binaryCoreEquiv a.LJ a.BJ).symm x) ((binaryCoreEquiv a.LJ a.BJ).symm y)
  obtain ⟨t⟩ := BinaryMS.MS93.exists_setup (hm.binaryInput e) hc'
  obtain ⟨common⟩ := t.commonFacts hc'
  by_cases hb : t.geometry.b t.reduction.radical = 4
  · obtain ⟨e',he⟩ := hm.distance_four_source_complete e hc t hb hs hS
    exact ⟨e',a.ms_natural_or_double h S hS e' he⟩
  have hlarge : 4 < t.geometry.b t.reduction.radical := by
    have he := t.geometry.even (BinaryMS.MS93.alpha t.reduction.radical) rfl
    change Even (t.geometry.b t.reduction.radical) at he
    obtain ⟨n,hn⟩ := he
    have hl := common.large_distance
    omega
  obtain ⟨e',hU⟩ := distance_eight_center_commutator_section hm e t common hlarge
  let : IsElementaryAbelian 2 (V.subgroupOf a.J) := IsElementaryAbelian.subgroupOf a.module_le_J
  have hR : a.BJ = a.inMSGroup.P.pCoreIn 2 := (a.PJ_core_of_msInput h).symm
  have hi : a.BJ.map a.inMSGroup.q = Matrix.PSL3Two.MarkedAutomorphisms.pointV :=
    a.BJ_image_of_msInput h
  exact (a.inMSGroup.not_case_four h hR hi S hS e' hU
    (hm.distance_eight_not_centralizer_core e t common hlarge hs hS)).elim

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.LocalControl.OriginalSource

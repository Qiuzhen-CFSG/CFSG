module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecializationRadical
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockSpecializationBlock
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.DistanceFourSource
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.AbelianSourceComplete
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightCenter

/-!
# The original fixed-line MS specialization without a universal classifier

The chosen four-space V is contained in the center of the literal core
C = [O₂(LR),L] and satisfies V = [V,L]. Its nontrivial fixed line does
not change this commutator-generation equality. A nonabelian core would
give an MS93 critical distance. At distance four Z(C) has order eight;
at larger distance [Z(C),L] has order eight. Each contains V, of order
sixteen, so the original core is abelian.

The complete abelian source theorem and the existing five-way comparison
then select the fixed-line alternative, with C = V. The retained quotient
marking supplies the original short group and linear-three block model.
The proper odd-index radical, relative Sylow T and original indecomposable
extension are constructed by the existing 12.4.6 source setup. No equality
between R and a natural-point radical, whole-core centrality or fixed-factor
identity is assumed. FixedBlockMSIndependentApplication connects the block
and both centralizer products to the existing fixed and moving consumers.

Source: Aschbacher--Smith 12.4.5--6, printed pp.813--814, and C.1.34,
pp.136--137; Meierfrankenfeld--Stellmacher (1993), (4.4)--(4.6).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02 ChapterC
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

private theorem no_large_distance_of_central_four_space {K R W : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple K R)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (t : BinaryMS.MS93.InputSetup (h.binaryInput e))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (hcard : Nat.card W = 16) (hWZ : W ≤ msCenter (msQ K R))
    (hm : W = ⁅W,K⁆) : False := by
  let A := K ⊔ R
  let U := ⁅msCenter (msQ K R),K⁆
  have hZA : msCenter (msQ K R) ≤ A :=
    (map_subtype_le (center (msQ K R))).trans (msQ_le_join K R)
  have hUA : U ≤ A := (@Subgroup.commutator_le_sup G _ _ _).trans
    (sup_le hZA le_sup_left)
  have hWA : W ≤ A := hWZ.trans hZA
  have hWU : W ≤ U := hm.le.trans (commutator_mono hWZ le_rfl)
  have hUsub : ⁅msCenter (msQ (K.subgroupOf A) (R.subgroupOf A)),K.subgroupOf A⁆ =
      U.subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [map_commutator,msQ_subgroupOf le_sup_left le_sup_right,
      centerIn_subgroupOf (msQ_le_join K R),map_subgroupOf_eq_of_le hZA,
      map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le hUA]
  obtain ⟨_,_,_,hU⟩ := t.center_source_sections common hb
  rw [hUsub] at hU
  have h8 : Nat.card (U.subgroupOf A) = 8 := natural_section_order _ hU
  have h16 : Nat.card (W.subgroupOf A) = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWA).toEquiv).trans hcard
  have hle := Nat.card_le_card_of_injective
    (inclusion (show W.subgroupOf A ≤ U.subgroupOf A from comap_mono hWU))
    (inclusion_injective _)
  omega

variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
namespace LocalGeometry
variable (d : LocalGeometry D)

/-- The literal MS commutator core is abelian under the original fixed-line
source hypotheses, without any universal MS classification input. -/
theorem ms_core_commutative_without_binary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    IsMulCommutative (msQ L d.R) := by
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  have hTV := ((structural G T L h).2.2 V D).1
  have hMS := d.smallMSPair h structural marked hmodel hne hescape
  have hVZ := d.module_le_ms_center ext h hTV
  have hV16 := module_card_sixteen ext hne
  by_contra hc
  have hc' : ¬ IsMulCommutative
      (BinaryMS.commutatorCore (L.subgroupOf (L ⊔ d.R))) := by
    intro hh
    apply hc
    apply isMulCommutative_iff.mpr
    intro x y
    apply (binaryCoreEquiv L d.R).symm.injective
    simpa only [map_mul] using isMulCommutative_iff.mp hh
      ((binaryCoreEquiv L d.R).symm x) ((binaryCoreEquiv L d.R).symm y)
  obtain ⟨t⟩ := BinaryMS.MS93.exists_setup (hMS.binaryInput ext.quotientEquiv) hc'
  obtain ⟨common⟩ := t.commonFacts hc'
  by_cases hb : t.geometry.b t.reduction.radical = 4
  · obtain ⟨e,hZ,_⟩ := hMS.distance_four_source_sections ext.quotientEquiv t common hb
    have h8 : Nat.card (msCenter (msQ L d.R)) = 8 := natural_section_order _ hZ
    have hle := card_le_of_le hVZ
    omega
  have hlarge : 4 < t.geometry.b t.reduction.radical := by
    have he := t.geometry.even (BinaryMS.MS93.alpha t.reduction.radical) rfl
    change Even (t.geometry.b t.reduction.radical) at he
    obtain ⟨n,hn⟩ := he
    have hl := common.large_distance
    omega
  exact no_large_distance_of_central_four_space hMS ext.quotientEquiv t common hlarge
    hV16 hVZ D.eq_commutator

/-- The fifth MS alternative and original linear-three block, retaining the
actual quotient marking and equality of the whole commutator core with V. -/
theorem ms_specialization_without_binary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      FixedMSAlternative L d.R T e ∧ msQ L d.R = V ∧ ChapterC.IsLinearTwoBlock L 3 := by
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  have hTV := ((structural G T L h).2.2 V D).1
  have hMS := d.smallMSPair h structural marked hmodel hne hescape
  have hc := d.ms_core_commutative_without_binary h structural marked hmodel hne hescape
  obtain ⟨e,he⟩ := hMS.abelian_source ext.quotientEquiv hc T
    (d.ms_sylow ext h hTV) inf_le_left
  obtain ⟨hcase,hQ⟩ := d.ms_fixed_alternative h structural marked hmodel hne hescape e he
  exact ⟨e,hcase,hQ,d.ms_isLinearTwoBlock h ext hmodel e hcase hQ⟩

/-- The same marking gives the intrinsic short group, block module and
identification of U(L) with the original indecomposable four-space. -/
theorem ms_markedBlock_without_binary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      FixedMSAlternative L d.R T e ∧ msQ L d.R = V ∧
      ChapterC.IsShort L ∧ ChapterC.IsLinearTwoBlock L 3 ∧
      (ChapterC.blockU L).map L.subtype = V ∧
      ∃ b : ChapterC.BlockModuleModel L naturalBinaryThreeAction, b.quotientIso = e := by
  obtain ⟨e,hc,hQ,hb⟩ := d.ms_specialization_without_binary h structural marked hmodel hne hescape
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  exact ⟨e,hc,hQ,d.ms_isShort h ext e hc hQ,hb,d.ms_blockU_eq hQ,
    d.ms_blockModel e hc hQ,d.ms_blockModel_quotientIso e hc hQ⟩

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

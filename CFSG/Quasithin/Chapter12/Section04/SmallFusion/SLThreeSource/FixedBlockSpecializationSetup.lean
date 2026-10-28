module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.LocalConstructionSupplement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Conditions
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.NormalCentralQuotientAction.KernelCriterion

/-!
# The original local group in the MS specialization

The kernel of the marked action is C_T(V)=O₂(LT), and it lies in
R=C_T(E). The full normalizer action therefore gives LR=LT. This
identifies the core and Sylow subgroup used in C.1.34 without treating
the index-two subgroup R as Sylow. The chosen commutator-generated V
lies in the center of the actual MS commutator subgroup.

Source: Aschbacher--Smith, proof of 12.4.6, printed p.814; C.1.31--34,
printed pp.135--137. Normality throughout is relative to LR.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry
variable (d : LocalGeometry D)

/-- The MS overgroup is the original LT, although R has index two in T. -/
theorem ms_join_eq (ext : SLThreeExtension D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    L ⊔ d.R = L ⊔ (T : Subgroup G) := by
  apply le_antisymm (sup_le_sup_left inf_le_left L)
  rw [join_eq_component_sup_core D ext hTV]
  apply sup_le_sup_left
  rw [← centralizer_eq_core D h hTV]
  exact inf_le_inf_left _ (centralizer_le d.le_module)

/-- The literal core in C.1.34 is C_T(V). -/
theorem ms_core_eq (ext : SLThreeExtension D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    (L ⊔ d.R).pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  rw [d.ms_join_eq ext h hTV]
  exact (centralizer_eq_core D h hTV).symm

/-- The actual ambient Sylow T is Sylow in LR. -/
theorem ms_sylow (ext : SLThreeExtension D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    Chapter1.IsSylowIn 2 (T : Subgroup G) (L ⊔ d.R) := by
  rw [d.ms_join_eq ext h hTV]
  exact ⟨T.subtype le_sup_right, map_subgroupOf_eq_of_le le_sup_right⟩

omit [Finite G] in
/-- L is normal in LR; no ambient subnormality in G is asserted. -/
theorem ms_relative_normal : (L.subgroupOf (L ⊔ d.R)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer (inf_le_left.trans D.sylow_normalizes_component))

/-- The original C-component restricts to the actual MS overgroup. -/
theorem ms_component (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (L.subgroupOf (L ⊔ d.R)).IsCComponent :=
  h.maximal_faithful.1.1.1.subgroupOf_of_le le_sup_left
    (sup_le_sup_left inf_le_left L)

omit [Finite G] in
/-- The literal product clause of MS1 follows from relative normality. -/
theorem ms_product : ∀ g ∈ L ⊔ d.R, ∃ l ∈ L, ∃ r ∈ d.R, l * r = g := by
  let := d.ms_relative_normal
  intro g hg
  have hm : (⟨g, hg⟩ : (L ⊔ d.R : Subgroup G)) ∈
      L.subgroupOf (L ⊔ d.R) ⊔ d.R.subgroupOf (L ⊔ d.R) := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
    trivial
  obtain ⟨l, hl, r, hr, he⟩ := mem_sup_of_normal_left.mp hm
  exact ⟨l, hl, r, hr, congrArg Subtype.val he⟩

/-- Characteristic two holds in the same LR, through its equality with LT. -/
theorem ms_characteristicTwo (ext : SLThreeExtension D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    HasCharacteristicTwo (L ⊔ d.R : Subgroup G) := by
  rw [d.ms_join_eq ext h hTV]
  exact Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
    (h.simpleQTKE.evenCharacteristic T)
    ⟨h.maximal_faithful.1.1.2.2, fun x hx =>
      (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) hx⟩)

/-- SQTK is inherited from the two-local normalizer of the original core. -/
theorem ms_sqtk (ext : SLThreeExtension D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    IsSQTK KnownSimple.IsKnownSimple (L ⊔ d.R : Subgroup G) := by
  rw [d.ms_join_eq ext h hTV]
  let H := L ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  have hHN : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hn : IsTwoLocal (normalizer (Q : Set G)) :=
    ⟨Q, h.maximal_faithful.1.1.2.2, isPGroup_pCoreIn 2 H, rfl⟩
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
    ((h.simpleQTKE.twoLocal_sqtk hn).subgroup (H.subgroupOf _))

/-- MS3 is the original escaping-normalizer argument with relative normality. -/
theorem ms_characteristic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    MSNoCharacteristicNormal L d.R := by
  intro C hc hn
  let := hc
  exact characteristic_eq_bot_of_normal_in_LR h structural
    uniquenessEarlier_knownSimple d.R inf_le_left d.index hescape C hn

/-- The original chosen V is in the actual MS commutator, not merely a section. -/
theorem module_le_msQ (ext : SLThreeExtension D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) : V ≤ msQ L d.R := by
  have hVC : V ≤ (L ⊔ d.R).pCoreIn 2 := by
    rw [d.ms_join_eq ext h hTV]
    exact D.le_core
  exact D.eq_commutator.le.trans (commutator_mono hVC le_rfl)

/-- V lies in the intrinsic center of the MS commutator, embedded in G. -/
theorem module_le_ms_center (ext : SLThreeExtension D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    V ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
      (msQ L d.R) := by
  have hq : msQ L d.R ≤ (L ⊔ d.R).pCoreIn 2 :=
    le_normalizer_iff_commutator_le_left.mp
      (le_sup_left.trans ((L ⊔ d.R).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (L ⊔ d.R) (pCore 2 _))))
  rw [d.ms_core_eq ext h hTV] at hq
  intro v hv
  exact ⟨⟨v, d.module_le_msQ ext h hTV hv⟩, mem_center_iff.mpr
    (fun q => Subtype.ext ((hq q.property).2 v hv).symm), rfl⟩

end LocalGeometry

omit [Finite G] in
/-- The marking supplies the derived rank-two quotient in MS1. -/
theorem ms_rankTwo (ext : SLThreeExtension D) : SmallRankTwoQuotient L := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply bot_unique
    intro x hx
    apply ext.quotientEquiv.map_eq_one_iff.mp
    exact Matrix.PSL3Two.center_eq_bot.le
      ((centerCongr ext.quotientEquiv ⟨x,hx⟩).property)
  have he := centralPreimage_eq_of_center_quotient_eq_bot (pCore 2 L) hz
  let := Atlas.sl_perfect 3 (by decide) (F := ZMod 2)
  exact Or.inl ⟨((QuotientGroup.quotientMulEquivOfEq he).trans ext.quotientEquiv).trans
    (topEquiv.symm.trans (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm))⟩

/-- All MS1 and MS3 clauses are discharged; the proper odd-index radical
witness is the remaining MS2(a) input. R is not claimed to be Sylow. -/
theorem smallMSPair_of_oddIndex
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (ext : SLThreeExtension D) (d : LocalGeometry D)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hradical : MSOddIndex L d.R) : SmallMSPair KnownSimple.IsKnownSimple L d.R := by
  have hTV := ((structural G T L h).2.2 V D).1
  exact ⟨inferInstance, d.ms_sqtk ext h hTV,
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (d.ms_characteristicTwo ext h hTV),
    d.ms_product, d.ms_component h, ms_rankTwo ext, hradical,
    d.ms_characteristic h structural hescape⟩

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

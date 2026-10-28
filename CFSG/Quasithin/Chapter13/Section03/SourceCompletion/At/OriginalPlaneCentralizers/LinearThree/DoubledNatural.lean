module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.LinearThree.DoubledNatural
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.BinaryMS


/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalPlaneCentralizers.LinearThree.DoubledNatural`.
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
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

theorem Context.perpendicular_le_msCoreCenter (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) :
    perpendicular d.coordinates ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (msQ J ((L ⊔ T).pCoreIn 2)) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := J ⊔ Q
  obtain ⟨i⟩ := s.component_has_binaryMS_input d J j
  obtain ⟨n,hnJ,hn⟩ := s.component_marked_cubic d J j
  have hEQ := chosen_perpendicular_central s d.coordinates
  have hEQ' : perpendicular d.coordinates ≤ Q := hEQ.trans (map_subtype_le _)
  have hEC : perpendicular d.coordinates ≤ centralizer (Q : Set G) := by
    intro x hx y hy
    obtain ⟨z,hz,rfl⟩ := hEQ hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y,hy⟩)
  have hcQ : D.pCoreIn 2 ≤ Q := by
    have h := map_mono (f := D.subtype) i.radical.twoCore_le
    change D.pCoreIn 2 ≤ (Q.subgroupOf D).map D.subtype at h
    rwa [map_subgroupOf_eq_of_le (show Q ≤ D from le_sup_right)] at h
  have hEcore : perpendicular d.coordinates ≤ D.pCoreIn 2 := by
    intro x hx
    refine ⟨⟨x,(le_sup_right : Q ≤ D) (hEQ' hx)⟩,i.core_selfCentralizing ?_,rfl⟩
    intro y hy
    exact Subtype.ext (hEC hx y.val (hcQ (mem_map_of_mem D.subtype hy)))
  have hUQ : msQ J Q ≤ Q := by
    change ⁅D.pCoreIn 2,J⁆ ≤ Q
    apply le_trans _ hcQ
    apply le_normalizer_iff_commutator_le_left.mp
    exact (le_sup_left : J ≤ D).trans (D.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image D (pCore 2 D)))
  have hEU : perpendicular d.coordinates ≤ msQ J Q := by
    rw [←perpendicular_commutator d.chart d.coordinates d.equivariant n hn,commutator_comm]
    exact commutator_mono hEcore (zpowers_le.mpr hnJ)
  intro x hx
  exact ⟨⟨x,hEU hx⟩,mem_center_iff.mpr (fun y =>
    Subtype.ext (hEC hx y.val (hUQ y.property))),rfl⟩

omit [Finite G] in
theorem perpendicular_inf_cubic_centralizer_eq_bot
    (d : MarkedPlane V) (n : normalizer (V : Set G))
    (hn : d.chart (V.normalizerMonoidHom.rangeRestrict n) = cubic) :
    perpendicular d.coordinates ⊓ centralizer ({n.val} : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  let v : Additive V := Additive.ofMul ⟨x,perpendicular_le d.coordinates hx.1⟩
  have hc : automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict n) v = v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change n.val * x * n.val⁻¹ = x
    rw [hx.2 n.val (Set.mem_singleton _),mul_inv_cancel_right]
  have hf : rho cubic (d.coordinates v) = d.coordinates v := by
    rw [←hn,←d.equivariant,hc]
  have hp := (mem_plane _).mp ((cubic_fixed_iff _).mp hf)
  have ho := (mem_orthogonal _).mp ((mem_coordinateGroup d.coordinates _ v).mp hx.1)
  have hz : d.coordinates v = 0 := by
    ext i
    fin_cases i
    · exact ho.1
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2.1
    · exact hp.2.2.2
    · exact ho.2
  have hv : v = 0 := d.coordinates.injective (by simpa using hz)
  exact congrArg (fun z : Additive V => z.toMul.val) hv

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Subgroup Theory.GroupTheory
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem section_card_bound {B W F : Type*} [Group B] [AddCommGroup W]
    [Field F] [Module F W] [Finite W] (A D C E : Subgroup G)
    (a : A →* B) (ρ : Representation F B W)
    (hs : HasSectionModel A D C a ρ) (hED : E ≤ D) (hEC : E ⊓ C = ⊥) :
    Nat.card E ≤ Nat.card W := by
  obtain ⟨_,_,_,hn,e,_⟩ := hs
  let := hn
  let f := (QuotientGroup.mk' (C.subgroupOf D)).comp (inclusion hED)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro x hx
    have hx' : QuotientGroup.mk' (C.subgroupOf D) (inclusion hED x) = 1 := hx
    have hc' : inclusion hED x ∈ C.subgroupOf D := (QuotientGroup.eq_one_iff _).mp hx'
    have hc : x.val ∈ C := hc'
    have hx1 : x.val = 1 := hEC.le ⟨x.property,hc⟩
    exact Subtype.ext hx1
  have h := Nat.card_le_card_of_injective f hf
  rw [Nat.card_congr e.toEquiv] at h
  exact h

private theorem natural_section_card (A D E : Subgroup G)
    (a : A →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (h : HasSectionModel A D ⊥ a (Representation.specialLinearNatural (k := ZMod 2) 3))
    (hED : E ≤ D) : Nat.card E ≤ 8 := by
  have hh := section_card_bound A D ⊥ E a _ h hED (inf_bot_eq E)
  norm_num only [Nat.card_fun,Nat.card_zmod,Nat.card_fin] at hh
  exact hh

/-- The perpendicular sixteen forces C.1.34(2), including its original common marking. -/
theorem double_natural_of_perpendicular (J R S E : Subgroup G)
    (x : G) (hxJ : x ∈ J) (hcard : Nat.card E = 16)
    (hEZ : E ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (msQ J R))
    (hm : ⁅zpowers x,E⁆ = E)
    (hf : E ⊓ centralizer ({x} : Set G) = ⊥)
    (e : Chapter1.XiQuotient J ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : MSModuleAlternatives J R S 1 (ZMod 2) e) :
    HasSectionModel J (msQ J R) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
        (Representation.specialLinearNatural (k := ZMod 2) 3)) ∧
      MSNotCentralizerCore J R S := by
  rcases hc with h1 | h2 | h3 | h4 | h5
  · have hh := natural_section_card J (msQ J R) E _ h1.2.2
      (hEZ.trans (map_subtype_le _))
    omega
  · exact h2
  · have hh := natural_section_card J (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (msQ J R)) E _ h3.1 hEZ
    omega
  · have hEU : E ≤ ⁅Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (msQ J R),J⁆ := by
      rw [←hm,commutator_comm]
      exact commutator_mono hEZ (zpowers_le.mpr hxJ)
    have hh := natural_section_card J _ E _ h4.2.2.2.2.2.1 hEU
    omega
  · have hEC : E ⊓ (msQ J R ⊓ centralizer (J : Set G)) = ⊥ := by
      apply le_bot_iff.mp
      intro y hy
      apply hf.le
      exact ⟨hy.1,fun z hz => (Set.mem_singleton_iff.mp hz) ▸ hy.2.2 x hxJ⟩
    have hh := section_card_bound J (msQ J R) _ E _ _ h5.2.2.1
      (hEZ.trans (map_subtype_le _)) hEC
    have hh' : Nat.card E ≤ 8 := by
      norm_num only [Nat.card_fun,Nat.card_zmod,Nat.card_fin] at hh
      exact hh
    omega

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Subgroup Theory.GroupTheory
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

theorem Context.double_natural_of_ms_alternatives (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) (S : Subgroup G)
    (e : Chapter1.XiQuotient J ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : MSModuleAlternatives J ((L ⊔ T).pCoreIn 2) S 1 (ZMod 2) e) :
    HasSectionModel J (msQ J ((L ⊔ T).pCoreIn 2)) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
        (Representation.specialLinearNatural (k := ZMod 2) 3)) ∧
      MSNotCentralizerCore J ((L ⊔ T).pCoreIn 2) S := by
  obtain ⟨n,hnJ,hn⟩ := s.component_marked_cubic d J j
  exact double_natural_of_perpendicular J _ S (perpendicular d.coordinates) n.val hnJ
    (perpendicular_card d.coordinates) (s.perpendicular_le_msCoreCenter d J j)
    (perpendicular_commutator d.chart d.coordinates d.equivariant n hn)
    (perpendicular_inf_cubic_centralizer_eq_bot d n hn) e hc

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- The binary specialization of the full C.1.34 implication, with all five rows. -/
@[expose] def BinaryMSClassification (G : Type*) [Group G] : Prop :=
  ∀ J R : Subgroup G, SmallMSPair KnownSimple.IsKnownSimple J R →
    Nonempty (Chapter1.XiQuotient J ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    ∀ S : Subgroup G, Chapter1.IsSylowIn 2 S (J ⊔ R) → R ≤ S →
      ∃ e : Chapter1.XiQuotient J ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        MSModuleAlternatives J R S 1 (ZMod 2) e

/-- This is precisely a specialization of the existing full source producer. -/
theorem binaryMSClassification_of_earlier
    (earlier : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple) : BinaryMSClassification G := by
  intro J R hms he S hS hRS
  exact earlier.linearThree G J R hms 1 (by decide) (ZMod 2) (by simp) he S hS hRS

theorem Context.component_smallMSPair (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) :
    SmallMSPair KnownSimple.IsKnownSimple J ((L ⊔ T).pCoreIn 2) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := J ⊔ Q
  obtain ⟨i⟩ := s.component_has_binaryMS_input d J j
  obtain ⟨e⟩ := s.binary_linearThree_core_model d J j
  have hz : center (J ⧸ pCore 2 J) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact e.map_eq_one_iff.mp (Matrix.PSL3Two.center_eq_bot.le ((centerCongr e) ⟨x,hx⟩).property)
  have he : centralPreimage (pCore 2 J) = pCore 2 J := by
    change (center (J ⧸ pCore 2 J)).comap (QuotientGroup.mk' _) = _
    rw [hz]
    exact QuotientGroup.ker_mk' _
  let := ChapterC.BinaryMS.binary_perfect
  refine {
    finite := inferInstance
    sqtk := i.sqtk
    fitting := i.fitting
    component := i.component
    rankTwo := Or.inl ⟨((QuotientGroup.quotientMulEquivOfEq he).trans e).trans
      (topEquiv.symm.trans (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm))⟩
    product := ?_
    radical := ?_
    characteristic := ?_ }
  · intro g hg
    obtain ⟨a,ha,b,hb,h⟩ := i.product ⟨g,hg⟩
    exact ⟨a.val,ha,b.val,hb,congrArg Subtype.val h⟩
  · obtain ⟨P,hP,ho,hc⟩ := i.radical
    have hp : (P.map D.subtype).subgroupOf D = P := by
      exact comap_map_eq_self_of_injective D.subtype_injective _
    refine ⟨P.map D.subtype,lt_of_le_of_ne (map_subtype_le _) ?_,?_,?_⟩
    · intro hh
      have htop : P = ⊤ := by rw [←hp,hh,subgroupOf_self]
      exact hP.ne htop
    · rw [hp]
      exact ho
    · rw [←map_pCoreIn_of_injective 2 P D.subtype D.subtype_injective]
      change (P.pCoreIn 2).map D.subtype = Q
      change P.pCoreIn 2 = Q.subgroupOf D at hc
      rw [hc,map_subgroupOf_eq_of_le (show Q ≤ D from le_sup_right)]
  · intro C hC hn
    let a : Q ≃* Q.subgroupOf D := (subgroupOfEquivOfLe le_sup_right).symm
    let C' := C.map a.toMonoidHom
    have hC' : C'.Characteristic := by
      apply characteristic_iff_le_comap.mpr
      intro b x hx
      obtain ⟨y,hy,rfl⟩ := hx
      exact ⟨(a.trans (b.trans a.symm)) y,
        (characteristic_iff_le_comap.mp hC (a.trans (b.trans a.symm))) hy,
        a.apply_symm_apply _⟩
    have hmap : C'.map (Q.subgroupOf D).subtype = (C.map Q.subtype).subgroupOf D := by
      apply map_injective D.subtype_injective
      rw [map_subgroupOf_eq_of_le ((map_subtype_le C).trans le_sup_right),map_map,map_map]
      rfl
    let := hC'
    have hzero := i.characteristic.eq_bot_of_normal C' (hmap.symm ▸ hn)
    exact (map_eq_bot_iff_of_injective C a.injective).mp hzero

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Subgroup Theory.GroupTheory
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

theorem Context.component_ms_alternatives (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (earlier : BinaryMSClassification G)
    (S : Subgroup G) (hS : Chapter1.IsSylowIn 2 S (J ⊔ (L ⊔ T).pCoreIn 2))
    (hQS : (L ⊔ T).pCoreIn 2 ≤ S) :
    ∃ e : Chapter1.XiQuotient J ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      MSModuleAlternatives J ((L ⊔ T).pCoreIn 2) S 1 (ZMod 2) e := by
  exact earlier J _ (s.component_smallMSPair d J j)
    (s.binary_linearThree_core_model d J j) S hS hQS

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Subgroup Theory.GroupTheory
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

theorem Context.component_doubled_natural (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (earlier : BinaryMSClassification G)
    (S : Subgroup G) (hS : Chapter1.IsSylowIn 2 S (J ⊔ (L ⊔ T).pCoreIn 2))
    (hQS : (L ⊔ T).pCoreIn 2 ≤ S) :
    ∃ e : Chapter1.XiQuotient J ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      HasSectionModel J (msQ J ((L ⊔ T).pCoreIn 2)) ⊥ (linearThreeActor e)
        ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
          (Representation.specialLinearNatural (k := ZMod 2) 3)) ∧
        MSNotCentralizerCore J ((L ⊔ T).pCoreIn 2) S := by
  obtain ⟨e,he⟩ := s.component_ms_alternatives d J j earlier S hS hQS
  exact ⟨e,s.double_natural_of_ms_alternatives d J j S e he⟩

theorem Context.exists_component_doubled_natural (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (earlier : BinaryMSClassification G) :
    ∃ S : Subgroup G, Chapter1.IsSylowIn 2 S (J ⊔ (L ⊔ T).pCoreIn 2) ∧
      (L ⊔ T).pCoreIn 2 ≤ S ∧
      ∃ e : Chapter1.XiQuotient J ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        HasSectionModel J (msQ J ((L ⊔ T).pCoreIn 2)) ⊥ (linearThreeActor e)
          ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
            (Representation.specialLinearNatural (k := ZMod 2) 3)) ∧
          MSNotCentralizerCore J ((L ⊔ T).pCoreIn 2) S := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let D := J ⊔ Q
  obtain ⟨i⟩ := s.component_has_binaryMS_input d J j
  obtain ⟨P,hP⟩ := i.radical.isPGroup.exists_le_sylow
  let S := (P : Subgroup D).map D.subtype
  have hs : Chapter1.IsSylowIn 2 S D := ⟨P,rfl⟩
  have hqs : Q ≤ S := by
    have hh := map_mono (f := D.subtype) hP
    rwa [map_subgroupOf_eq_of_le (show Q ≤ D from le_sup_right)] at hh
  exact ⟨S,hs,hqs,s.component_doubled_natural d J j earlier S hs hqs⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Subgroup Theory.GroupTheory
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The doubled-natural assertion identifies the whole commutator core,
with the same original component quotient acting on both summands. -/
theorem doubled_natural_card {J R : Subgroup G}
    (e : Chapter1.XiQuotient J ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (h : HasSectionModel J (msQ J R) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
        (Representation.specialLinearNatural (k := ZMod 2) 3))) : Nat.card (msQ J R) = 64 := by
  obtain ⟨_,_,_,hn,a,_⟩ := h
  let := hn
  have hb : (⊥ : Subgroup G).subgroupOf (msQ J R) = ⊥ := bot_subgroupOf _
  let b := (QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot
  have hc := Nat.card_congr (b.symm.trans a).toEquiv
  change Nat.card (msQ J R) = Nat.card ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) at hc
  norm_num only [Nat.card_prod,Nat.card_fun,Nat.card_zmod,Nat.card_fin] at hc
  exact hc

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Subgroup Theory.GroupTheory
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G]

/-- The full doubled-natural section has an elementary abelian underlying group. -/
theorem doubled_natural_elementary {J R : Subgroup G}
    (e : Chapter1.XiQuotient J ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (h : HasSectionModel J (msQ J R) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
        (Representation.specialLinearNatural (k := ZMod 2) 3))) :
    IsElementaryAbelian 2 (msQ J R) := by
  obtain ⟨_,_,_,hn,a,_⟩ := h
  let := hn
  have hb : (⊥ : Subgroup G).subgroupOf (msQ J R) = ⊥ := bot_subgroupOf _
  let b := (QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot
  let c := b.symm.trans a
  refine { toIsMulCommutative := ⟨⟨fun x y => c.injective (by
    simp only [map_mul,mul_comm])⟩⟩, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  apply c.injective
  rw [map_pow,map_one,pow_two]
  apply Multiplicative.toAdd.injective
  change (c x).toAdd + (c x).toAdd = 0
  ext i <;> exact CharTwo.add_self_eq_zero _

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Subgroup Theory.GroupTheory
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- The original commutator core is E64 under the exact earlier classification. -/
theorem Context.component_msCore_elementary_card (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J)
    (earlier : BinaryMSClassification G) :
    IsElementaryAbelian 2 (msQ J ((L ⊔ T).pCoreIn 2)) ∧
      Nat.card (msQ J ((L ⊔ T).pCoreIn 2)) = 64 := by
  obtain ⟨S,_,_,e,he,_⟩ := s.exists_component_doubled_natural d J j earlier
  exact ⟨doubled_natural_elementary e he,doubled_natural_card e he⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers

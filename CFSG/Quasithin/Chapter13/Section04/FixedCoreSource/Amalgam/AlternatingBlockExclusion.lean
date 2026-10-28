module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.AlternatingHeadBudget
public import Theory.Representation.BinaryAlternatingSixModels.PairedNearMaximum
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.ParabolicSection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ShortBlockBudget
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.ResidualBound
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Bounds
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme

/-!
# The four-chief-factor obstruction in the alternating amalgam

The two inequivalent natural heads of the original omega module make each
component cubic move at least six dimensions, giving three contributions
to its cubic length. Inside the actual second component parabolic, the
self-centralizing four-core supplies a further contribution above the full
O₂(X) kernel. Restriction to O²(B) therefore proves that every complete
chief series has at least four noncentral binary factors.

For literal K₂=L₂ the original short five-dimensional block instead gives
at most three. This excludes the short-block alternative in the selected
A₆ branch without a supplied cubic, chief count, outer movement bound or
maximum-family inclusion. AlternatingPlaneExclusion constructs the marked
plane application and discharges shortness in the ordinary original row.
Model selection and the general 13.4.7 alternatives remain source duties.
Source: Aschbacher–Smith 13.4.7(4), printed pp.902–903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Section03.Noncentrality.SupercriticalSource NoncentralChiefRefinement
open Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
variable (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Theory.SpecificGroups.SymmetricSix.A6)
include h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB hK hres eK

open Theory.SpecificGroups.SymmetricSix BinaryDuadModule BinaryAlternatingSix

/-- Every cubic in the component has at least three contributions on the
whole original omega module, from its two inequivalent natural heads. -/
theorem original_pair_alternating_omega_cubic_length
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (E : Subgroup G) (hE : Nat.card E = 3) (hEC : E ≤ K.map (A ⊔ B).subtype) :
    3 ≤ conjugationCubicLength E
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  obtain ⟨he,e,_,hbudget⟩ := original_pair_alternating_paired_budget h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  let := he
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hk : f.ker = pCore 2 C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hE' : Nat.card (E.subgroupOf C) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv).trans hE
  have hc : Nat.card ((E.subgroupOf C).map f) = 3 :=
    GLS3.Chapter5.cubic_image_card_of_two_kernel f (hk ▸ pCore_isPGroup) _ hE'
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := (E.subgroupOf C).map f)
    3 (by rw [hc])
  have ha' : orderOf (a : A6) = 3 := (Subgroup.orderOf_coe a).trans ha
  have hgen : zpowers (a : A6) = (E.subgroupOf C).map f :=
    eq_of_le_of_card_ge (zpowers_le.mpr a.property) (by rw [Nat.card_zpowers,ha',hc])
  have hsix := paired_cubic_movement (a : A6) ha'
  rw [hgen] at hsix
  have hd := hsix.trans (hbudget (E.subgroupOf C)).1
  rw [Representation.conjugation_length_eq_log_fixedCodim C U
    ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X)) E hEC]
  exact (show 3 = Nat.log 4 (2 ^ 6) from rfl).trans_le
    (Nat.log_mono_right (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd))

/-- A cubic in the actual component parabolic also contributes above O₂(X).
The kernel is the full intersection with O₂(X), including outer actors. -/
theorem original_pair_alternating_outer_cubic_length
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (E : Subgroup G) (hE : Nat.card E = 3)
    (hEJ : E ≤ B ⊓ K.map (A ⊔ B).subtype) :
    1 ≤ sectionCubicLength E ((A ⊔ B).pCoreIn 2) (B.pCoreIn 2) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let J := B ⊓ C
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  obtain ⟨_,e,hmarks,_⟩ := original_pair_alternating_paired_budget h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  let fC := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  let j : J ≃* B.subgroupOf C := {
    toFun x := ⟨⟨x.val,x.property.2⟩,x.property.1⟩
    invFun x := ⟨x.val.val,x.property,x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  let eP := MulEquiv.subgroupCongr hmarks.2.1
  let f := eP.toMonoidHom.comp ((fC.subgroupMap (B.subgroupOf C)).comp j.toMonoidHom)
  have hf : Function.Surjective f := eP.surjective.comp
    ((fC.subgroupMap_surjective _).comp j.surjective)
  have hKC := original_pair_component_action_kernel h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB hres K hK
  have hns : ¬ Group.IsSolvable X := by
    intro hs
    let := hs
    exact hK.not_isSolvable inferInstance
  have hXC := original_pair_full_action_kernel h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB hres hns
  have hkC : fC.ker = pCore 2 C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hk : f.ker = (X.pCoreIn 2).subgroupOf J := by
    ext x
    change eP ((fC.subgroupMap (B.subgroupOf C)) (j x)) = 1 ↔ x.val ∈ X.pCoreIn 2
    rw [eP.map_eq_one_iff,Subtype.ext_iff]
    change fC (⟨x.val,x.property.2⟩ : C) = 1 ↔ _
    change (⟨x.val,x.property.2⟩ : C) ∈ fC.ker ↔ _
    rw [hkC]
    have heq : (⟨x.val,x.property.2⟩ : C) ∈ pCore 2 C ↔ x.val ∈ C.pCoreIn 2 :=
      (mem_map_iff_mem C.subtype_injective).symm
    rw [heq,←hKC,←hXC]
    exact and_congr_left (fun _ => iff_of_true x.property.2 ((show B ≤ X from le_sup_right) x.property.1))
  have hTX : (T : Subgroup G) ≤ X := hTB.trans le_sup_right
  have hQT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow X (T.subtype hTX)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX] at hh
  have hXN : X ≤ normalizer (X.pCoreIn 2 : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hQB : X.pCoreIn 2 ≤ B.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 X) (hQT.trans hTB) (le_sup_right.trans hXN)
  have hnK := (original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).1
  have hXK : X ≤ normalizer (C : Set G) := by
    let := hnK
    have hh := K.le_normalizer_map X.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hBJ : B ≤ normalizer (J : Set G) :=
    (le_inf B.le_normalizer (le_sup_right.trans hXK)).trans inf_normalizer_le_normalizer_inf
  have hJR : J.pCoreIn 2 ≤ B.pCoreIn 2 := pCoreIn_mono_of_normalizes inf_le_left hBJ
  let : ((X.pCoreIn 2).subgroupOf (B.pCoreIn 2)).Normal :=
    normal_subgroupOf_of_le_normalizer ((B.pCoreIn_le 2).trans (le_sup_right.trans hXN))
  exact CubicComparison.section_pos_of_selfCentralizing_core_image E (B.pCoreIn 2)
    (X.pCoreIn 2) J hE (isPGroup_pCoreIn 2 B) hQB
    ((hEJ.trans inf_le_left).trans (B.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image B (pCore 2 B))))
    ((hEJ.trans inf_le_left).trans (le_sup_right.trans hXN)) hEJ hJR f hf hk
    a6SynthemeCore_centralizer.le

/-- The literal second two-residual has at least four noncentral binary
chief factors in the selected A₆ branch. The cubic is constructed in B. -/
theorem original_pair_alternating_residual_chief_lower
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (t : ChiefSeries ((pResidual 2 B).map B.subtype))
    (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) : 4 ≤ t.noncentralTwoCount := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  have hd : 3 ∣ Nat.card B := by
    rw [SymmetricThreeTwoCore.card_eq eB]
    exact dvd_mul_of_dvd_left (by decide : 3 ∣ 6) _
  obtain ⟨E₀,hE₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := B) 3
    (n := 1) (by simpa using hd)
  let E := E₀.map B.subtype
  have hE : Nat.card E = 3 :=
    (card_map_of_injective B.subtype_injective).trans (by simpa using hE₀)
  have hEB : E ≤ B := map_subtype_le _
  have hEX : E ≤ X := hEB.trans le_sup_right
  have hEC : E ≤ C := by
    intro x hx
    have hr := (original_pair_component_is_residual h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK).1
    have hxR : (⟨x,hEX hx⟩ : X) ∈ pResidual 2 X := by
      apply mem_pResidual_of_orderOf_coprime
      rw [←Subgroup.orderOf_coe (⟨x,hEX hx⟩ : X)]
      exact (show Nat.Coprime 2 (Nat.card E) by rw [hE]; decide).of_dvd_right
        (E.orderOf_dvd_natCard hx)
    exact mem_map_of_mem X.subtype (hr ▸ hxR)
  have homega := original_pair_alternating_omega_cubic_length h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL E hE hEC
  have houter := original_pair_alternating_outer_cubic_length h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL E hE
    (le_inf hEB hEC)
  have hUX : U ≤ X := conjugateSpanBy_le (fun z hz =>
    (hTA.trans le_sup_left) ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hr := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  have hUQ : U ≤ X.pCoreIn 2 := by
    have hh := map_mono (f := X.subtype) hr.le_pCore
    rwa [map_subgroupOf_eq_of_le hUX] at hh
  have hmono := conjugationCubicLength_mono E hUQ
  let eR := (pResidual 2 B).equivMapOfInjective B.subtype B.subtype_injective
  let t₀ := t.mapActor eR.symm
  have ht₀ := t.mapActor_complete eR.symm ht0 ht1
  have hb := CubicComparison.symmetricThree_core_length_le_residual_count
    eB E₀ (by simpa using hE₀) t₀ ht₀.1 ht₀.2
  have hbudget : conjugationCubicLength E (B.pCoreIn 2) ≤ t.noncentralTwoCount := by
    change conjugationCubicLength (E₀.map B.subtype) ((pCore 2 B).map B.subtype) ≤ _
    rw [CubicComparison.length_map_injective B.subtype B.subtype_injective E₀ (pCore 2 B)]
    exact hb.trans (t.mapActor_noncentralTwoCount eR.symm).le
  change 3 ≤ conjugationCubicLength E U at homega
  change 1 ≤ sectionCubicLength E (X.pCoreIn 2) (B.pCoreIn 2) at houter
  unfold sectionCubicLength at houter
  omega

/-- Alternative 13.2.2(10II) is impossible in the selected A₆ case of
13.4.7(4), retaining the literal equality of the two-residuals K₂=L₂. -/
theorem original_pair_alternating_short_block_impossible
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hb : ChapterC.IsShort L)
    (J : Subgroup G) (hJL : J ≤ L)
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (himage : (J.subgroupOf L).map
      ((alternatingGroup (Fin 6)).subtype.comp
        (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L)))) =
      Theory.SpecificGroups.SymmetricSix.synthemeStabilizer ⊓ alternatingGroup (Fin 6))
    (hK₂ : (pResidual 2 B).map B.subtype = (pResidual 2 J).map J.subtype) : False := by
  obtain ⟨s⟩ := SeriesOn.exists_series (⊤ : Subgroup ((pResidual 2 B).map B.subtype))
  have hl := original_pair_alternating_residual_chief_lower h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL
    s.series s.head_eq s.last_eq
  have hu : s.series.noncentralTwoCount ≤ 3 := by
    have hcount : ∀ t : ChiefSeries ((pResidual 2 B).map B.subtype),
        t.head = ⊥ → t.last = ⊤ → t.noncentralTwoCount ≤ 3 := by
      rw [hK₂]
      exact second_parabolic_residual_short_chief_budget D m hb J hJL hTJ himage
    exact hcount s.series s.head_eq s.last_eq
  omega

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam

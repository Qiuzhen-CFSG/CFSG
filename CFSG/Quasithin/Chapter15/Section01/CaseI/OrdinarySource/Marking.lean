module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceNineResidual
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
/-!
# The original ordinary component and its marked central-involution actions

The source Sylow intersection in G₁ supplies every hypothesis of1.1.5 for
all nonidentity elements of Ω₁(Z(T)). The complete earlier classifier then
acts on the same ordinary component selected by15.1.19. Its commutator
conclusion proves faithfulness and normalization. Trivial odd core identifies
Z(L) with O₂(L), preserving genuine central two-covers. Subnormal inheritance
inside M_Z proves characteristic two for the literal M_L=M_Z∩L.

The original Nine consumer retains the same marked vector, Sylow subgroup,
component and complementary planes. It discharges all marking/Sylow inputs;
ordinary component status is a branch condition on that chosen C-component.
The narrower15.1.20(3) parabolic catalogue and15.1.21 exclusions are not
asserted here.

Source: Aschbacher–Smith15.1.18(6),15.1.20(3), printed pp.1093,1095–1097,
using the complete earlier1.1.5(3).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original central involutions have the full1.1.5 inputs on the
same component centralizer and its supplied Sylow intersection. -/
theorem ordinary_involution_inputs (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hsyl : Chapter1.IsSylowIn 2 d.S d.G1) :
    ∃ P : Sylow 2 d.G1, (P : Subgroup d.G1).map d.G1.subtype = d.S ∧
      ∀ z ∈ centralInvolutions T, z ≠ 1 → Chapter1.Lemma115Hypotheses d.G1 P Mc z := by
  obtain ⟨P,hP⟩ := hsyl
  refine ⟨P,hP,?_⟩
  intro z hz hzne
  let := h.elementary
  exact CaseIMarkedSubgroup.central_involution_hypotheses hG hu d.Z1_ne_bot
    (IsElementaryAbelian.of_le (d.Z1_le_fixed.trans inf_le_left)) P
    (hP.le.trans d.S_le_T) hz hzne

/-- Literal ordinary-component center: the odd core vanishes on the
original L, so the center is its two-core, including central covers. -/
theorem ordinary_center (d : CaseIComponentData T M Mc V)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hodd : pPrimeCore 2 d.G1 = ⊥) :
    center d.L = pCore 2 d.L ∧ IsPGroup 2 (center d.L) := by
  let e : d.L.subgroupOf d.G1 ≃* d.L := subgroupOfEquivOfLe d.L_component.1
  let := hL.2
  let := IsQuasisimple.of_mulEquiv e
  have hoddL : pPrimeCore 2 d.L = ⊥ := by
    have hh := pPrimeCore_map_iso 2 e
    rw [Subgroup.IsSubnormal.pPrimeCore_eq_bot hodd _ hL.1,Subgroup.map_bot] at hh
    exact hh.symm
  have he := IsQuasisimple.center_eq_pCore hoddL
  exact ⟨he,by rw [he]; exact pCore_isPGroup⟩

/-- The original ML has characteristic two by subnormal inheritance
inside MZ, and contains the original SL as a proper subgroup of L. -/
theorem ordinary_intersection (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) :
    HasCharacteristicTwo d.ML ∧ d.SL ≤ d.ML ∧ d.ML < d.L := by
  let := h.elementary
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hTM)
    simpa only [map_subgroupOf_eq_of_le h.le_selected, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTM] using map_mono (f := M.subtype) hh
  have hZT : d.Z1 ≤ (T : Subgroup G) :=
    (d.Z1_le_fixed.trans inf_le_left).trans hVT
  let : IsElementaryAbelian 2 d.Z1 :=
    IsElementaryAbelian.of_le (d.Z1_le_fixed.trans inf_le_left)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMZ : HasCharacteristicTwo d.MZ := Chapter1.mem_He_iff.mp
    (CaseIMarkedSubgroup.partner_centralizer_characteristic_two hG hu
      (IsElementaryAbelian.isPGroup 2 d.Z1) hZT)
  let A := d.L.subgroupOf d.G1
  let B := d.MZ.subgroupOf d.G1
  let eB : B ≃* d.MZ := subgroupOfEquivOfLe (show d.MZ ≤ d.G1 from inf_le_left)
  have hB : HasCharacteristicTwo B := hMZ.of_equiv eB.symm
  have hAB : HasCharacteristicTwo (A.subgroupOf B) :=
    subnormal_core_selfCentralizing hB (A.subgroupOf B) hL.1.subgroupOf
  let e : A.subgroupOf B ≃* d.ML := {
    toFun x := ⟨x.val.val, x.val.property, x.property⟩
    invFun x := ⟨⟨⟨x, x.property.1.1⟩,x.property.1⟩,x.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  refine ⟨hAB.of_equiv e,?_,?_⟩
  · exact le_inf (le_inf (inf_le_left.trans d.S_le_G1)
      ((inf_le_left.trans d.S_le_T).trans hTMc)) inf_le_right
  · exact lt_of_le_of_ne inf_le_right (fun he => d.L_not_le_MZ (he ▸ inf_le_left))

/-- Complete earlier1.1.5 actions for the literal ordinary source component.
Every nontrivial original central involution moves all of L; this proves
faithfulness and normalization without assuming an abstract model action. -/
theorem ordinary_marked_actions (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hsyl : Chapter1.IsSylowIn 2 d.S d.G1)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) :
    centralInvolutions T ≤ normalizer (d.L : Set G) ∧
      centralInvolutions T ⊓ centralizer (d.L : Set G) = ⊥ ∧
      ∀ z ∈ centralInvolutions T, z ≠ 1 →
        ⁅d.L,zpowers z⁆ = d.L ∧ HasModelAction115 (d.L.subgroupOf d.G1) z := by
  obtain ⟨P,hP,h115⟩ := d.ordinary_involution_inputs hG hu h hsyl
  have hs (z : G) (hz : z ∈ centralInvolutions T) (hne : z ≠ 1) :
      ⁅d.L,zpowers z⁆ = d.L ∧ HasModelAction115 (d.L.subgroupOf d.G1) z := by
    have hh := Chapter1.lemma_1_1_5_three_knownSimple hG d.G1 P Mc z
      (h115 z hz hne) (d.L.subgroupOf d.G1) hL
    rw [map_subgroupOf_eq_of_le (show d.L ≤ d.G1 from d.L_component.1)] at hh
    exact ⟨hh.1.symm,hh.2.2⟩
  have hn : centralInvolutions T ≤ normalizer (d.L : Set G) := by
    intro z hz
    by_cases he : z = 1
    · exact he ▸ (normalizer (d.L : Set G)).one_mem
    obtain ⟨α,ha,_⟩ := (hs z hz he).2
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      let x' : d.L.subgroupOf d.G1 := ⟨⟨x,d.L_component.1 hx⟩,hx⟩
      change z*x*z⁻¹ ∈ d.L
      rw [←ha x']
      exact (α x').property
    · intro x hx
      let x' : d.L.subgroupOf d.G1 := ⟨⟨x,d.L_component.1 hx⟩,hx⟩
      obtain ⟨y,hy⟩ := α.surjective x'
      refine ⟨y,y.property,?_⟩
      change z*(y : G)*z⁻¹ = x
      rw [←ha y,hy]
  refine ⟨hn,?_,hs⟩
  apply bot_unique
  intro z hz
  by_contra he
  have hzne : z ≠ 1 := fun hh => he (mem_bot.mpr hh)
  have hc := commutator_eq_bot_iff_le_centralizer.mpr (zpowers_le.mpr hz.2)
  rw [commutator_comm,(hs z hz.1 hzne).1] at hc
  exact d.L_not_le_MZ (hc ▸ bot_le)

/-- Source data for the same ordinary component, retaining its exact
Sylow and characteristic-two local intersection and every marked action. -/
structure OrdinarySource (d : CaseIComponentData T M Mc V) : Prop where
  center_eq : center d.L = pCore 2 d.L
  center_two : IsPGroup 2 (center d.L)
  local_characteristicTwo : HasCharacteristicTwo d.ML
  sylow_le_local : d.SL ≤ d.ML
  local_proper : d.ML < d.L
  central_normalizes : centralInvolutions T ≤ normalizer (d.L : Set G)
  central_faithful : centralInvolutions T ⊓ centralizer (d.L : Set G) = ⊥
  actions : ∀ z ∈ centralInvolutions T, z ≠ 1 →
    ⁅d.L,zpowers z⁆ = d.L ∧ HasModelAction115 (d.L.subgroupOf d.G1) z

/-- Discharge the source marking of an ordinary component from the original
ambient hypotheses, odd-core result and literal Sylow witness. -/
theorem ordinarySource (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hsyl : Chapter1.IsSylowIn 2 d.S d.G1)
    (hodd : pPrimeCore 2 d.G1 = ⊥)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) : d.OrdinarySource := by
  obtain ⟨hc,hc2⟩ := d.ordinary_center hL hodd
  obtain ⟨hct,hle,hlt⟩ := d.ordinary_intersection hG hu h hTM hL
  obtain ⟨hn,hf,ha⟩ := d.ordinary_marked_actions hG hu h hsyl hL
  exact ⟨hc,hc2,hct,hle,hlt,hn,hf,ha⟩

end CaseIComponentData

/-- The actual source Nine choice, with its same-marker planes and ordinary
model actions. All Sylow and1.1.5 inputs are constructed internally. The only
branch premise is that the selected C-component is ordinary. -/
theorem PreparedChosenModule.source_caseI_nine_ordinary_marking
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.row = .four ∧ Nat.card d.Z1 = 2 ∧
      pPrimeCore 2 d.G1 = ⊥ ∧ IsQuasisimple (d.L ⧸ pCore 2 d.L) ∧
      d.L ∈ Chapter1.L G d.S ∧ Chapter1.IsSylowIn 2 d.SL d.L ∧
      Chapter1.IsSylowIn 2 d.S d.G1 ∧ ¬ d.L ≤ M ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) → d.OrdinarySource) ∧
      let R := (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
      let V1 := V ⊓ centralizer (R : Set G)
      let V2 := ⁅V,R⁆
      V2 ≤ V ∧ R ⊔ V2 ≤ normalizer (d.L : Set G) ∧ ⁅d.L,V2⁆ ≠ ⊥ ∧
      Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧ V1 ⊔ V2 = V ∧ V1 ⊓ V2 = ⊥ ∧ d.Z1 ≤ V1 := by
  let := h.elementary
  obtain ⟨v,K,hv,hfixed,hK,hgen,hcard,hSyl,hbound⟩ :=
    chosen_nine_marked_image_with_movement T hM.1.2 h.normalized h9
  obtain ⟨d,hdZ,hdrow,hdcard,hodd,hq,hL,hSL,hV2,hn,hmove⟩ :=
    h.caseI_component_of_marked_image hG T hempty hM hmany hJ hu hne hfull h9 hres
      v K hv hfixed hK hgen hcard hSyl hbound
  obtain ⟨hZ,_,_,hSylZ⟩ := marked_zpowers_and_sylow_of_image_stabilizer
    T hM.1.2 h.normalized v hv hfixed K hK hgen hSyl
  have hSylG : Chapter1.IsSylowIn 2 d.S d.G1 := by
    change Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (d.Z1 : Set G))
      (centralizer (d.Z1 : Set G))
    rw [hdZ]
    apply h.caseI_centralizer_sylow hG T hM hJ hZ
    rw [inf_comm (centralizer (zpowers (v.toMul : G) : Set G)) M]
    exact hSylZ
  refine ⟨d,hdrow,hdcard,hodd,hq,hL,hSL,hSylG,d.L_not_le_M hG T hempty hM hu,
    d.ordinarySource hG hu h hM.1.2 hSylG hodd,hV2,?_,hmove,?_⟩
  · have he : normalizer (d.Z1 : Set G) = centralizer (d.Z1 : Set G) :=
      le_antisymm (normalizer_le_centralizer_of_card_two d.Z1 hdcard)
        (Subgroup.centralizer_le_normalizer _)
    rw [he] at hn
    exact hn
  · let P (Z : Subgroup G) : Prop :=
      let C := M ⊓ centralizer (Z : Set G)
      let R := (pResidual 2 C).map C.subtype
      let V1 := V ⊓ centralizer (R : Set G)
      let V2 := ⁅V,R⁆
      Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧ V1 ⊔ V2 = V ∧ V1 ⊓ V2 = ⊥ ∧ Z ≤ V1
    have hp : P (zpowers (v.toMul : G)) := source_nine_planes T h.normalized h9 v K hv hK hcard
    exact (congrArg P hdZ).mpr hp
end CFSG.Quasithin.Chapter15.Section01

module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceFixedPlaneMovement
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceNineResidual
/-!
# One original Nine marker for movement and residual escape

The Case-I selection is made once. The residual-intersection argument proves
that its actual cubic actor escapes M_Z; the literal Sylow plane exchange
proves fixed-plane noncentrality for its actual C-component in each recognized
cubic quotient row. Keeping these conclusions in one existential packet
allows the ordinary model comparison to consume both without equating
independently selected components.

Source: Aschbacher--Smith15.1.18(2),15.1.24(3--4),15.1.25(3),
printed pp.1092,1101--1102. The earlier15.1.14 input remains explicit.
-/
public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
theorem PreparedChosenModule.source_caseI_nine_fixed_plane_movement_and_escape
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
      let R := (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
      let V1 := V ⊓ centralizer (R : Set G)
      let V2 := ⁅V,R⁆
      Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧ V1 ⊔ V2 = V ∧ V1 ⊓ V2 = ⊥ ∧
      d.Z1 ≤ V1 ∧ d.S.relIndex (T : Subgroup G) = 2 ∧
      ¬ (primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype ≤ d.MZ ∧
      (Facts (d.L ⧸ pCore 2 d.L) → ¬ V1 ≤ centralizer (d.L : Set G)) := by
  let := h.elementary
  obtain ⟨v,K,hv,hfixed,hK,hgen,hcard,hSyl,hbound⟩ :=
    chosen_nine_marked_image_with_movement T hM.1.2 h.normalized h9
  obtain ⟨d,hdZ,hdrow,hdcard,hodd,hq,hL,hSL,hV2,hn,hmove⟩ :=
    h.caseI_component_of_marked_image hG T hempty hM hmany hJ hu hne hfull h9 hres
      v K hv hfixed hK hgen hcard hSyl hbound
  let C := M ⊓ d.G1
  let R := (pResidual 2 C).map C.subtype
  let V1 := V ⊓ centralizer (R : Set G)
  let V2 := ⁅V,R⁆
  let Y := (primeToResidual 3 C).map C.subtype
  have hC : C = M ⊓ centralizer (zpowers (v.toMul : G) : Set G) := by
    change M ⊓ centralizer (d.Z1 : Set G) = _
    rw [hdZ]
  have hplanes : Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧ V1 ⊔ V2 = V ∧
      V1 ⊓ V2 = ⊥ ∧ d.Z1 ≤ V1 := by
    let P (Z : Subgroup G) : Prop :=
      let R := (pResidual 2 (M ⊓ centralizer (Z : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z : Set G)).subtype
      Nat.card (V ⊓ centralizer (R : Set G) : Subgroup G) = 4 ∧ Nat.card (⁅V,R⁆ : Subgroup G) = 4 ∧
        (V ⊓ centralizer (R : Set G)) ⊔ ⁅V,R⁆ = V ∧
        (V ⊓ centralizer (R : Set G)) ⊓ ⁅V,R⁆ = ⊥ ∧
        Z ≤ V ⊓ centralizer (R : Set G)
    have hp : P (zpowers (v.toMul : G)) := source_nine_planes T h.normalized h9 v K hv hK hcard
    exact (congrArg P hdZ).mpr hp
  have haction : d.S.relIndex (T : Subgroup G) = 2 ∧
      ∀ t ∈ (T : Subgroup G), t ∉ d.S →
        V2.map (MulAut.conj t).toMonoidHom = V1 := by
    let P (Z : Subgroup G) : Prop :=
      let S := (T : Subgroup G) ⊓ centralizer (Z : Set G)
      let R := (pResidual 2 (M ⊓ centralizer (Z : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z : Set G)).subtype
      S.relIndex (T : Subgroup G) = 2 ∧
        ∀ t ∈ (T : Subgroup G), t ∉ S →
          ⁅V,R⁆.map (MulAut.conj t).toMonoidHom = V ⊓ centralizer (R : Set G)
    have hp : P (zpowers (v.toMul : G)) := by
      obtain ⟨hi,_,_,_,he⟩ := source_nine_plane_action T hM.1.2 h.normalized h9 v K hv hK hcard hSyl
      exact ⟨hi,fun t ht hs => (he t ht hs).2⟩
    exact (congrArg P hdZ).mpr hp
  have hV2ne : V2 ≠ ⊥ := by
    intro he
    have hc := hplanes.2.1
    rw [he,card_bot] at hc
    omega
  have hYid : (primeToResidual 3 Y).map Y.subtype = Y := by
    rw [←map_embedded_primeToResidual_of_hom 3 (primeToResidual 3 C) C.subtype,
      embedded_primeToResidual_eq_of_normal 3 (primeToResidual 3 C) le_rfl]
  have he : ⁅V,Y⁆ = V2 := by
    dsimp only [Y,V2,R]
    rw [hC]
    exact marked_primeToResidual_commutator M V h.normalized v K hK hcard
  have hYp : IsPPerfect 2 Y := (isPPerfect_primeToResidual 3 2 (by decide)).of_surjective
    ((primeToResidual 3 C).equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom
    ((primeToResidual 3 C).equivMapOfInjective C.subtype C.subtype_injective).surjective
  have hYV : Y ≤ normalizer (V : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans h.normalized
  have hV2Y : ⁅V2,Y⁆ = V2 := by
    rw [←he]
    exact commutator_isPPerfect_idempotent Y V hYp (IsElementaryAbelian.isPGroup 2 V) hYV
  have hYnon : ¬ Y ≤ centralizer (V : Set G) := by
    intro hc
    have hh := commutator_eq_bot_iff_le_centralizer.mpr hc
    rw [commutator_comm,he] at hh
    exact hV2ne hh
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMnot : ¬ M ≤ Mc := fun hm => hne (hM.1.1.eq_of_le hMc.1.1 hm)
  have hNMc : M ⊓ centralizer (V : Set G) ≤ Mc := by
    rw [hfull]
    exact inf_le_right.trans (localModule_centralizer_le_partner T M hu)
  obtain ⟨hZ,hZne,hgenZ,hSylZ⟩ := marked_zpowers_and_sylow_of_image_stabilizer
    T hM.1.2 h.normalized v hv hfixed K hK hgen hSyl
  have hprime : letI := caseI_module_centralizer_normal (Z1 := zpowers (v.toMul : G)) h.normalized
      (Nat.card (pResidual 2 ((M ⊓ centralizer (zpowers (v.toMul : G) : Set G) : Subgroup G) ⧸
        (M ⊓ centralizer (V : Set G)).subgroupOf
          (M ⊓ centralizer (zpowers (v.toMul : G) : Set G))))).Prime := by
    let := caseI_module_centralizer_normal (Z1 := zpowers (v.toMul : G)) h.normalized
    have hh := marked_quotient_card M V h.normalized v K hK (zpowers_le.mpr v.toMul.property)
    rw [card_twoResidual_of_card_six (hh.trans hcard)]
    decide
  have hI := caseI_residual_intersection T M Mc V (zpowers (v.toMul : G))
    h.normalized (zpowers_le.mpr v.toMul.property) hNMc hTMc hMnot hgenZ hSylZ hprime
  have hYout : ¬ Y ≤ d.MZ := by
    intro hb
    have hYH : Y ≤ M ⊓ Mc ⊓ centralizer (zpowers (v.toMul : G) : Set G) := by
      intro y hy
      have hc : y ∈ C := map_subtype_le _ hy
      exact ⟨⟨hc.1,(hb hy).2⟩,by simpa only [CaseIComponentData.G1,hdZ] using hc.2⟩
    have hh := embedded_pResidual_mono 2 hYH
    rw [(pResidual_eq_top_iff 2 Y).mpr hYp,
      ←MonoidHom.range_eq_map,range_subtype,hI] at hh
    exact hYnon (hh.trans ((map_subtype_le _).trans inf_le_right))
  obtain ⟨t,ht,htS⟩ : ∃ t ∈ (T : Subgroup G), t ∉ d.S := by
    by_contra! hh
    have he := relIndex_eq_one.mpr hh
    rw [haction.1] at he
    contradiction
  refine ⟨d,hdrow,hdcard,hodd,hq,hL,hSL,hplanes.1,hplanes.2.1,hplanes.2.2.1,
    hplanes.2.2.2.1,hplanes.2.2.2.2,haction.1,hYout,?_⟩
  intro hf
  let := hq
  exact d.fixed_plane_not_centralizes hG hf V1 V2 Y hplanes.2.2.2.2
    ((IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left) hV2ne hYid hV2Y t
    (haction.2 t ht htS)
end CFSG.Quasithin.Chapter15.Section01

module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceOutside
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedCubicResidual
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceNinePlanes
public import Theory.GroupTheory.PResidual.PrimeToPerfect

/-!
# Cubic control on the original Nine component and planes

One original marker supplies both the source component and its two planes.
The perfect component escapes M. The literal Y=O^{3'}(C_M(Z1)) has the
same cubic action as the two-residual, normalizes the component, and escapes
MZ by the source residual-intersection identity. Its fixed and moved
four-groups are complementary in V; the fixed plane contains Z1 and lies
in C_S(Y). Every two-perfect subgroup of Y outside MZ moves all of V2 and
has centralizer index three on it.

Only the earlier15.1.14(1) residual-centralization premise remains explicit.
The component/parabolic catalogue and final15.1.25--29 exclusion are separate
source obligations; this module does not assert15.1.15.

Source: Aschbacher--Smith15.1.20(1),15.1.24(3)--(4), printed pp.1094,1101.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Original Nine source component with its literal complementary planes,
cubic actor, and all subgroup movement/index conclusions of15.1.24(3). -/
theorem PreparedChosenModule.source_caseI_nine_cubic_control
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
      d.L ∈ Chapter1.L G d.S ∧ Chapter1.IsSylowIn 2 d.SL d.L ∧ ¬ d.L ≤ M ∧
      let C := M ⊓ d.G1
      let R := (pResidual 2 C).map C.subtype
      let V1 := V ⊓ centralizer (R : Set G)
      let V2 := ⁅V,R⁆
      let Y := (primeToResidual 3 C).map C.subtype
      Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧ V1 ⊔ V2 = V ∧ V1 ⊓ V2 = ⊥ ∧
      d.Z1 ≤ V1 ∧ V1 ≤ d.S ⊓ centralizer (Y : Set G) ∧
      ¬ Y ≤ d.MZ ∧ Y ≤ normalizer (d.L : Set G) ∧ V2 ≤ V ∧ ⁅d.L,V2⁆ ≠ ⊥ ∧
      ⁅V,Y⁆ = V2 ∧ ⁅V2,Y⁆ = V2 ∧ (centralizer (V2 : Set G)).relIndex Y = 3 ∧
      ∀ Y0 : Subgroup G, Y0 ≤ Y → IsPPerfect 2 Y0 → ¬ Y0 ≤ d.MZ →
        ⁅V,Y0⁆ = V2 ∧ ⁅V2,Y0⁆ = V2 ∧ (centralizer (V2 : Set G)).relIndex Y0 = 3 := by
  let := h.elementary
  obtain ⟨v,K,hv,hfixed,hK,hgen,hcard,hSyl,hbound⟩ :=
    chosen_nine_marked_image_with_movement T hM.1.2 h.normalized h9
  obtain ⟨d,hdZ,hr,hz,ho,hq,hlocal,hsyl,hV2V,hnL,hmove⟩ :=
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
  have hp : IsPPerfect 2 (primeToResidual 3 C) := isPPerfect_primeToResidual 3 2 (by decide)
  have hYp : IsPPerfect 2 Y := hp.of_surjective
    ((primeToResidual 3 C).equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom
    ((primeToResidual 3 C).equivMapOfInjective C.subtype C.subtype_injective).surjective
  have hYR : Y ≤ R := map_mono (le_pResidual_of_isPPerfect _ hp)
  have he : ⁅V,Y⁆ = V2 := by
    dsimp only [Y,V2,R]
    rw [hC]
    exact marked_primeToResidual_commutator M V h.normalized v K hK hcard
  have hNZ : normalizer (d.Z1 : Set G) = d.G1 :=
    le_antisymm (normalizer_le_centralizer_of_card_two d.Z1 hz)
      (Subgroup.centralizer_le_normalizer _)
  rw [hNZ] at hnL
  have hYn : Y ≤ normalizer (d.L : Set G) := hYR.trans (le_sup_left.trans hnL)
  have hV2ne : V2 ≠ ⊥ := by
    intro hb
    apply hmove
    change ⁅d.L,V2⁆ = ⊥
    rw [hb,commutator_bot_right]
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
  have hplanes : Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧ V1 ⊔ V2 = V ∧ V1 ⊓ V2 = ⊥ ∧
      d.Z1 ≤ V1 := by
    let P (Z : Subgroup G) : Prop :=
      let C := M ⊓ centralizer (Z : Set G)
      let R := (pResidual 2 C).map C.subtype
      let V1 := V ⊓ centralizer (R : Set G)
      let V2 := ⁅V,R⁆
      Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧ V1 ⊔ V2 = V ∧ V1 ⊓ V2 = ⊥ ∧ Z ≤ V1
    have hp : P (zpowers (v.toMul : G)) :=
      source_nine_planes T h.normalized h9 v K hv hK hcard
    exact (congrArg P hdZ).mpr hp
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hM.1.2)
    simpa only [map_subgroupOf_eq_of_le h.le_selected, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hM.1.2] using map_mono (f := M.subtype) hh
  have hV1SY : V1 ≤ d.S ⊓ centralizer (Y : Set G) :=
    le_inf (le_inf (inf_le_left.trans hVT)
      (inf_le_left.trans (V.le_centralizer.trans
        (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))))
      (inf_le_right.trans (centralizer_le hYR))
  have hmain := marked_cubic_subgroup_movement M V h.normalized v K hK hcard
  rw [←hC] at hmain
  have hself := hmain Y le_rfl hYp hYnon
  refine ⟨d,hr,hz,ho,hq,hlocal,hsyl,d.L_not_le_M hG T hempty hM hu,
    hplanes.1,hplanes.2.1,hplanes.2.2.1,hplanes.2.2.2.1,hplanes.2.2.2.2,hV1SY,
    hYout,hYn,hV2V,hmove,he,hself.2.1,hself.2.2,?_⟩
  intro Y0 hY0 hp0 hout
  apply hmain Y0 hY0 hp0
  intro hc
  apply hout
  exact le_inf ((hY0.trans (map_subtype_le _)).trans inf_le_right)
    (hc.trans (by rw [hfull]; exact localModule_centralizer_le_partner T M hu))

end CFSG.Quasithin.Chapter15.Section01

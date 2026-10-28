module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection

/-!
# Application of the marker construction to the actual Nine action

The orthogonal marking supplies the nonzero line, local Sylow group and
central seed. Its stabilizer of order six gives the faithful residual of
order three. Applying the new construction then obtains the component
without using the later exchanged-source theorem.

Source: Aschbacher--Smith 15.1.16(b)--20, printed pp.1092--1094.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual Nine action constructs the earlier marker, before the
component theorem is invoked. -/
theorem chosen_nine_preExclusionMarker
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (h9 : SourceCases.Nine (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict)) :
    ∃ m : CaseIPreExclusionMarker T M V hn,
      m.row = .four ∧ m.prime = 3 ∧ Nat.card m.Z1 = 2 ∧
      ∀ {Mc : Subgroup G} (d : CaseIComponentData T M Mc V),
        d.Z1 = m.Z1 → d.row = m.row → d.ExchangedPlaneGeometry := by
  obtain ⟨v,K,hv,hfixed,hK,hgen,hcard,hSyl,hbound⟩ :=
    chosen_nine_marked_image_with_movement T hTM hn h9
  obtain ⟨hZ,hZne,hgenZ,hSylZ⟩ :=
    marked_zpowers_and_sylow_of_image_stabilizer T hTM hn v hv hfixed K hK hgen hSyl
  let Z1 := zpowers (v.toMul : G)
  have hZcard : Nat.card Z1 = 2 := by
    rw [Nat.card_zpowers]
    apply orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ v.toMul.property)
    intro he
    apply hv
    apply Additive.toMul.injective
    exact Subtype.ext he
  have hres : letI := caseI_module_centralizer_normal (Z1 := Z1) hn
      Nat.card (pResidual 2 ((M ⊓ centralizer (Z1 : Set G) : Subgroup G) ⧸
        (M ⊓ centralizer (V : Set G)).subgroupOf (M ⊓ centralizer (Z1 : Set G)))) = 3 := by
    let := caseI_module_centralizer_normal (Z1 := Z1) hn
    apply card_twoResidual_of_card_six
    exact (marked_quotient_card M V hn v K hK (zpowers_le.mpr v.toMul.property)).trans hcard
  let m : CaseIPreExclusionMarker T M V hn := {
    row := .four
    Z1 := Z1
    prime := 3
    prime_prime := Nat.prime_three
    marked_fixed := hZ
    marked_nontrivial := hZne
    generates := hgenZ
    local_sylow := hSylZ
    sylow_normal := chosen_nine_centralizer_normal T hTM hn (hZ.trans inf_le_left) h9
    residual_card := hres
    seed_bound := marked_fixedSpace_seed_bound T hn v K hK hbound }
  refine ⟨m,rfl,rfl,hZcard,?_⟩
  intro Mc d hdZ hdrow
  have hplanes := source_nine_planes T hn h9 v K hv hK hcard
  have haction := source_nine_plane_action T hTM hn h9 v K hv hK hcard hSyl
  let R := (pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
    (M ⊓ centralizer (Z1 : Set G)).subtype
  let V1 := V ⊓ centralizer (R : Set G)
  let V2 := ⁅V,R⁆
  have hF : d.nineFixedPlane = V1 :=
    congrArg (fun Z : Subgroup G => V ⊓ centralizer
      ((pResidual 2 (M ⊓ centralizer (Z : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z : Set G)).subtype : Set G)) hdZ
  have hV2 : d.nineMovingPlane = V2 :=
    congrArg (fun Z : Subgroup G => ⁅V,
      (pResidual 2 (M ⊓ centralizer (Z : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z : Set G)).subtype⁆) hdZ
  have hS : d.S = (T : Subgroup G) ⊓ centralizer (Z1 : Set G) :=
    congrArg (fun Z : Subgroup G => (T : Subgroup G) ⊓ centralizer (Z : Set G)) hdZ
  refine {
    sizes := Or.inl ⟨hdrow,?_,?_,?_⟩
    planes_sup := ?_
    planes_inf := ?_
    marked_le_fixed := ?_
    index := ?_
    fixes_planes := ?_
    fixed_centralizer_index := ?_
    exchanges := ?_ }
  · simpa only [hdZ] using hZcard
  · simpa only [hF] using hplanes.1
  · simpa only [hV2] using hplanes.2.1
  · simpa only [hF,hV2] using hplanes.2.2.1
  · simpa only [hF,hV2] using hplanes.2.2.2.1
  · simpa only [hdZ,hF] using hplanes.2.2.2.2
  · simpa only [hS] using haction.1
  · simpa only [hS,hF,hV2] using (And.intro haction.2.1 haction.2.2.1)
  · simpa only [hS,hF] using haction.2.2.2.1
  · simpa only [hS,hF,hV2] using haction.2.2.2.2

/-- An actual source-action consumer of the construction before exclusions.
The earlier global residual is its only additional source hypothesis. -/
theorem PreparedChosenModule.source_nine_preExclusion_component
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
      d.PreExclusionSource h.normalized 3 ∧ d.ExchangedPlaneGeometry := by
  let := h.elementary
  obtain ⟨m,hr,hp,hc,hplanes⟩ := chosen_nine_preExclusionMarker T hM.1.2 h.normalized h9
  obtain ⟨d,hZ,hd,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hd.trans hr,by simpa only [hZ] using hc,hp ▸ s,hplanes d hZ hd⟩

/-- Run the general component and cubic-plane arguments on an actual Nine
action. This checks all the new interfaces against the literal source maps. -/
theorem PreparedChosenModule.source_nine_exchanged_from_marker
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
    ∃ d : CaseIComponentData T M Mc V, d.ExchangedSource := by
  obtain ⟨d,_,_,s,g⟩ := h.source_nine_preExclusion_component
    hG T hempty hM hmany hJ hu hne hfull h9 hres
  exact ⟨d,s.exchangedSource hG h g⟩

end CFSG.Quasithin.Chapter15.Section01

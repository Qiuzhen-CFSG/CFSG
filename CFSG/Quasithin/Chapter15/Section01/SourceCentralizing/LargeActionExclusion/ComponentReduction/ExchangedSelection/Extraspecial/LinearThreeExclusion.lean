module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.ResidualExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.LinearThree.ResidualAction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.BinaryLinearThreeCubic
public import Theory.Representation.ExtraspecialBinarySix.LargeSubspaceKernel

/-!
# Excluding the binary SL3 block on the original extraspecial component

The second parabolic residual moves the whole original four-dimensional
moving space and contains it. The central-preimage prime-to-three residual
normalizes the same component by original 1.2.1(3). Together with the marked
centralizer residual its faithful image contains the distinct central and
noncentral cubics. A Sylow three-subgroup still covers that image.

The extraspecial action is faithful on the moving four-space, whereas an
odd actor on a subgroup of a natural binary SL3 block has image of order
at most three. Thus the two cubic images would coincide, contradicting the
original noncentral marking. No exchange or false containment of the whole
local-core center in U(L) is used.

Source: Aschbacher--Smith 15.1.16(c), 15.1.24(1--2), and 1.2.1(3),
printed pp.1092 and 1101. This replaces the obstructed central cubic lift
without changing its residual convention or the chosen component.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The parabolic residual acts nontrivially before any exchange hypothesis. -/
theorem PreExclusionSource.linearThreeY_not_centralizes
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} (s : d.PreExclusionSource h.normalized 3)
    (hTM : (T : Subgroup G) ≤ M)
    (a : d.ConstrainedL3Alternative) :
    ¬ d.nineMovingPlane ≤ centralizer (d.linearThreeY : Set G) := by
  have hVS := s.moving_le_sylow (h := h) hTM
  intro hc
  have hr : (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype ≤
      d.linearThreeY := map_mono primeToResidual_three_le_twoResidual
  have hVL := ((le_inf hVS (hc.trans (centralizer_le hr))).trans a.centralizers.le).trans
    inf_le_right
  exact s.moving_noncentral (by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hVL)

/-- The original cubic residual gives the same movement and action kernel. -/
theorem PreExclusionSource.linearThree_residual_action
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative) :
    ⁅V,d.linearThreeY⁆ = d.nineMovingPlane ∧
      ⁅d.nineMovingPlane,d.linearThreeY⁆ = d.nineMovingPlane ∧
      d.linearThreeY.pCoreIn 2 ≤ centralizer (V : Set G) ∧
      (¬ d.linearThreeY ≤ d.MZ) ∧
      (centralizer (V : Set G)).relIndex d.linearThreeY = 3 ∧
      V ⊓ centralizer (d.linearThreeY : Set G) = d.nineFixedPlane := by
  have hYC : d.linearThreeY ≤ M ⊓ d.G1 := (map_subtype_le _).trans
    (inf_le_inf_left M d.L_component.1)
  have hp : IsPPerfect 2 d.linearThreeY := isPPerfect_embedded_pResidual 2 _
  have hne : ¬ d.linearThreeY ≤ centralizer (V : Set G) := by
    intro hc
    exact sp.linearThreeY_not_centralizes (h := h) hTM a
      ((show d.nineMovingPlane ≤ V from le_normalizer_iff_commutator_le_left.mp
        (((map_subtype_le _).trans inf_le_left).trans h.normalized)).trans
          (le_centralizer_iff.mp hc))
  obtain ⟨h1,h2,h3,hi,hfix⟩ := sp.moving_of_noncentral_twoPerfect (h := h) hYC hp hne
  exact ⟨h1,h2,h3,(fun he => hne (sp.twoPerfect_intersection_centralizes (h := h) hp
    (hYC.trans inf_le_left) he)),hi,hfix⟩

/-- The original plane lies in the center of the second parabolic residual core. -/
theorem PreExclusionSource.linearThree_moving_in_core_center
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative)
    (hplanes : d.nineFixedPlane ⊔ d.nineMovingPlane = V) :
    d.nineMovingPlane ≤ d.linearThreeY.pCoreIn 2 ⊓
      centralizer (d.linearThreeY.pCoreIn 2 : Set G) := by
  obtain ⟨hm,hm2,hcore,_⟩ := sp.linearThree_residual_action (h := h) hTM a
  have hVnL : V ≤ normalizer (d.L : Set G) := by
    exact hplanes.ge.trans (sup_le
      ((a.fixedPlane_centralizes hTM h).trans (Subgroup.centralizer_le_normalizer _))
      (le_sup_right.trans sp.residual_normalizes))
  have hVnP : V ≤ normalizer ((M ⊓ d.L : Subgroup G) : Set G) :=
    le_normalizer_inf (h.le_selected.trans M.le_normalizer) hVnL
  have hVnY : V ≤ normalizer (d.linearThreeY : Set G) :=
    hVnP.trans (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))
  have hV2Y : d.nineMovingPlane ≤ d.linearThreeY :=
    hm ▸ le_normalizer_iff_commutator_le_right.mp hVnY
  have hV2V : d.nineMovingPlane ≤ V := by
    exact le_sup_right.trans hplanes.le
  let := h.elementary
  exact le_inf (le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 V).to_le hV2V) hV2Y
    (le_normalizer_iff_commutator_le_left.mpr hm2.le))
    (hV2V.trans (le_centralizer_iff.mp hcore))


end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterD ChapterD.UniqueFactor Section03
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem twoPerfect_mark_normalizer
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {A : Subgroup G} (hp : IsPPerfect 2 A)
    (hAn : A ≤ normalizer (d.Z1 : Set G)) : A ≤ normalizer (d.L : Set G) := by
  let N := normalizer (d.Z1 : Set G)
  have hLN : d.L ≤ N := d.L_component.1.trans (Subgroup.centralizer_le_normalizer _)
  have hL : (d.L.subgroupOf N).IsCComponent :=
    d.L_isCComponent_in_G1.in_normalizer_of_centralizes d.L_component.1 le_rfl
  let := h.elementary
  have htwo : IsPGroup 2 d.Z1 :=
    (IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left)
  have hN := hG.twoLocal_sqtk ⟨d.Z1,d.Z1_ne_bot,htwo,rfl⟩
  have hquot : IsSQTK KnownSimple.IsKnownSimple (N ⧸ pCore 2 N) := by
    refine ⟨?_,hN.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 N) pCore_isPGroup).trans
      (hN.stronglyQuasithin p hp ho)
  have hAp : IsPPerfect 2 (A.subgroupOf N) := hp.of_surjective
    (subgroupOfEquivOfLe hAn).symm.toMonoidHom (subgroupOfEquivOfLe hAn).symm.surjective
  have hn := Chapter1.Section02.twoPerfect_normalizes_cComponent_source hquot hL hAp
  have hh := (map_mono (f := N.subtype) hn).trans
    ((d.L.subgroupOf N).le_normalizer_map N.subtype)
  rwa [map_subgroupOf_eq_of_le hAn,map_subgroupOf_eq_of_le hLN] at hh

/-- The two independent cubic images on the original moving four-space exclude
the natural binary SL3 block, without using exchanged planes. -/
theorem PreExclusionSource.no_extraspecial_l3
    {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (sp : d.PreExclusionSource h.normalized 3)
    (hTM : (T : Subgroup G) ≤ M)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (c : letI := h.elementary; ExtraspecialMarker.ImageMarking T M V h.normalized)
    (hZ : letI := h.elementary; d.Z1 = ExtraspecialMarker.fixedSubgroup M V h.normalized c.X)
    (hplanes : d.nineFixedPlane ⊔ d.nineMovingPlane = V) :
    ¬ d.ConstrainedL3Alternative := by
  let := h.elementary
  intro a
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  let P := pResidual 2 D
  let Z := (center P).map P.subtype
  let X := c.X.map P.subtype
  let W := subspaceCommutator ρ ⊤ X
  let A := (primeToResidual 3 (ExtraspecialMarker.centralPreimage M V h.normalized)).map
    (ExtraspecialMarker.centralPreimage M V h.normalized).subtype
  let R := d.nineResidual
  obtain ⟨hAM,hAn,_,_,_⟩ := c.central_primeToResidual_movement T h.normalized hex
  change A ≤ M at hAM
  rw [←hZ] at hAn
  have hAp : IsPPerfect 2 A := (isPPerfect_primeToResidual 3 2 (by decide)).of_surjective
    ((primeToResidual 3 (ExtraspecialMarker.centralPreimage M V h.normalized)).equivMapOfInjective
      (ExtraspecialMarker.centralPreimage M V h.normalized).subtype
      (ExtraspecialMarker.centralPreimage M V h.normalized).subtype_injective).toMonoidHom
    ((primeToResidual 3 (ExtraspecialMarker.centralPreimage M V h.normalized)).equivMapOfInjective
      (ExtraspecialMarker.centralPreimage M V h.normalized).subtype
      (ExtraspecialMarker.centralPreimage M V h.normalized).subtype_injective).surjective
  have hAL : A ≤ normalizer (d.L : Set G) :=
    d.twoPerfect_mark_normalizer (h := h) hG hAp hAn
  have hRM : R ≤ M := (map_subtype_le _).trans inf_le_left
  have hRL : R ≤ normalizer (d.L : Set G) := le_sup_left.trans sp.residual_normalizes
  have hAim : (A.subgroupOf M).map f = Z :=
    ExtraspecialMarker.centralPreimage_primeToResidual_image T h.normalized hex
  have hRim : (R.subgroupOf M).map f = X := by
    have hh := ExtraspecialMarker.residual_action_image M V h.normalized (fixedSpace ρ X)
    dsimp only at hh
    rw [c.residual] at hh
    rw [MonoidHom.range_comp,inclusion_range] at hh
    change (d.nineResidual.subgroupOf M).map f = X
    unfold nineResidual G1
    rw [hZ]
    exact hh
  have hmove : d.nineMovingPlane.subgroupOf V = binarySubgroup W := by
    have hh := (ExtraspecialMarker.residual_spaces M V h.normalized (fixedSpace ρ X)).2
    rw [c.residual] at hh
    unfold nineMovingPlane nineResidual G1
    rw [hZ]
    exact hh
  have hWL : (binarySubgroup W).map V.subtype ≤ d.L := by
    rw [←hmove,map_subgroupOf_eq_of_le (show d.nineMovingPlane ≤ V from
      le_sup_right.trans hplanes.le)]
    exact ((sp.linearThree_moving_in_core_center (h := h) hTM a hplanes).trans inf_le_left).trans
      ((pCoreIn_le 2 _).trans ((map_subtype_le _).trans inf_le_right))
  let H := A ⊔ R
  have hHM : H ≤ M := sup_le hAM hRM
  have hHL : H ≤ normalizer (d.L : Set G) := sup_le hAL hRL
  let F := f.comp (inclusion hHM)
  have hF : F.range = Z ⊔ X := by
    rw [MonoidHom.range_comp,inclusion_range]
    rw [subgroupOf_sup hAM hRM,Subgroup.map_sup,hAim,hRim]
  have hFP : F.range ≤ P := by rw [hF]; exact sup_le (map_subtype_le _) (map_subtype_le _)
  have hWdim := (ExtraspecialMarker.source_image_planes T h.normalized hex
    c.X c.card_X c.noncentral).2.1
  obtain ⟨_,_,_,hP,hcard,_,hdim,_⟩ := hex
  let := hP
  have hpF : IsPGroup 3 F.range := (IsExtraspecial.isPGroup 3 P).to_le hFP
  let Q : Sylow 3 H := Classical.choice inferInstance
  let Q' := Q.mapSurjective F.rangeRestrict_surjective
  have hQ' : (Q' : Subgroup F.range) = ⊤ :=
    (Q'.is_maximal' (hpF.to_subgroup ⊤) le_top).symm
  let B := (Q : Subgroup H).map H.subtype
  have hBH : B ≤ H := map_subtype_le _
  let g := f.comp (inclusion (hBH.trans hHM))
  have hg : g.range = F.range := by
    have hh := congrArg (Subgroup.map F.range.subtype) hQ'
    change ((Q : Subgroup H).map F.rangeRestrict).map F.range.subtype = _ at hh
    rw [Subgroup.map_map,MonoidHom.subtype_comp_rangeRestrict,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    rw [←hh,MonoidHom.range_comp,inclusion_range]
    change (B.subgroupOf M).map f = (Q : Subgroup H).map F
    have hB : B.subgroupOf M = (Q : Subgroup H).map (inclusion hHM) := by
      apply map_injective M.subtype_injective
      rw [map_subgroupOf_eq_of_le (hBH.trans hHM),Subgroup.map_map]
      rfl
    rw [hB,Subgroup.map_map]
  have hdiv : Nat.card g.range ∣ 3 := a.block.cubic_image_card_dvd
    (Q.isPGroup'.map H.subtype) (hBH.trans hHL) hWL g (by
      intro b hb
      have hk : g b ∈ subspaceKernel ρ W P := by
        refine ⟨hFP (hg ▸ (show g b ∈ g.range from ⟨b,rfl⟩)),?_⟩
        intro w hw
        apply Additive.toMul.injective
        apply Subtype.ext
        change (b : G) * (w.toMul : G) * (b : G)⁻¹ = w.toMul
        rw [hb w.toMul (mem_map_of_mem V.subtype hw),mul_inv_cancel_right]
      have hker := Representation.ExtraspecialBinarySix.large_subspaceKernel_eq_bot ρ
        (imageRepresentation_injective M V h.normalized) P hcard hdim W (by
          change Module.finrank (ZMod 2) W = 4 at hWdim
          omega)
      exact hker.le hk)
  rw [hg,hF] at hdiv
  have hZ3 : Nat.card Z = 3 := by
    rw [card_map_of_injective P.subtype_injective]
    exact IsExtraspecial.center_order_p 3 P
  have hX3 : Nat.card X = 3 := by
    rw [card_map_of_injective P.subtype_injective]
    exact c.card_X
  have hle : Z ⊔ X = Z := (eq_of_le_of_card_ge le_sup_left (by
    rw [hZ3]
    exact Nat.le_of_dvd (by decide) hdiv)).symm
  have hXZ : X ≤ Z := by rw [←hle]; exact le_sup_right
  have he : X = Z := eq_of_le_of_card_ge hXZ (by rw [hZ3,hX3])
  exact c.noncentral ((map_injective P.subtype_injective) he)
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

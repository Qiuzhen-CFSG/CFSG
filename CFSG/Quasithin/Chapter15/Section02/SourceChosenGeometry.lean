module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Definitions
public import CFSG.Quasithin.Chapter15.Section01.CentralizingControl
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.Elementary
public import CFSG.Quasithin.ChapterE.Section03.Parameters.FourDimensional
public import CFSG.Quasithin.ChapterE.Section03.OddCore.SolvableApplication

/-!
# Numerical and elementary geometry for the source plane in Section 15.2

The actual chosen action has m=2 and a=1, even before excluding proper
support. The quadratic ratio supplies an involution; the four-space has no
FF offender. The earlier source solvability and reduced-image theorems then
give a=1. Baumann control applies to every subgroup of the chosen module.

For a constructed plane normalized by an HStar member, the two-overgroup
conclusion of 15.2.5 controls its full normalizer. The two alternatives of
15.2.14(2) identify the plane with the omega-center of its literal centralizer
in T. These are conditional construction tools: offender existence and
normality, the residual recognition and full-support conclusion of 15.2.12,
and the action restrictions of 15.2.13--14 remain separate obligations.

Source: Aschbacher--Smith, 15.2.9--14, printed pp.1110--1112,
combined manuscript of 1 March 2004.
-/

public section

open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section02

open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor ChosenGeometry

variable {G : Type*} [Group G] [Finite G]

/-- The rank and displacement assertions of 15.2.10 for any quadratic
elementary actor in the actual chosen image. -/
theorem ChosenSmallSource.quadratic_actor
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V) :
    letI := h.prepared.elementary
    ∀ A : Subgroup (internalActionImage M V h.prepared.normalized),
      IsElementaryTwo A → IsQuadratic (imageRepresentation M V h.prepared.normalized) A →
        rank A = 1 ∧ fixedCodim (imageRepresentation M V h.prepared.normalized) A = 2 := by
  let := h.prepared.elementary
  exact fun _ hA hq => quadratic_actor_four_of_no_ff _ h.finrank_eq_four.le h.not_ff hA hq

/-- Original 15.2.14(6), for the actual image action, with no plane premise. -/
theorem ChosenSmallSource.module_parameters
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V) :
    letI := h.prepared.elementary
    ChapterE.moduleM (imageRepresentation M V h.prepared.normalized) = 2 ∧
      ChapterE.moduleA (imageRepresentation M V h.prepared.normalized) = 1 := by
  let := h.prepared.elementary
  let ρ := imageRepresentation M V h.prepared.normalized
  have hq : quadraticRatio ρ ≤ 2 := h.prepared.quadratic_ratio.le
  have hc : pCore 2 (internalActionImage M V h.prepared.normalized) = ⊥ := by
    rw [← chosenNormalizer_actionImage_eq T h.maximal.1.2 h.prepared.normalized]
    exact chosenNormalizer_actionImage_reduced T h.maximal.1.2 h.prepared.le_selected
      h.prepared.normalized h.prepared.seed_span
  obtain ⟨t, ht⟩ := ChapterE.exists_involution_of_quadraticRatio_le_two ρ hq
  have heven : Even (Nat.card (internalActionImage M V h.prepared.normalized)) :=
    even_iff_two_dvd.mpr (ht ▸ orderOf_dvd_natCard t)
  exact ⟨ChapterE.moduleM_eq_two_of_four_nonFF ρ h.finrank_eq_four.le h.not_ff hq,
    ChapterE.OddCore.moduleA_eq_one_of_solvable_of_even ρ
      (imageRepresentation_injective _ _ _)
      (source_chosen_action_isSolvable h.ambient T h.empty h.maximal V
        h.prepared.normalized h.prepared.le_local) hc heven⟩

/-- The source choice of H exists and lies in the designated partner.
Only the preceding quotient conclusion 15.2.8 is retained. -/
theorem ChosenSmallSource.exists_wreath_local
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hquotient : ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((H ⧸ pCore 2 H) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    ∃ H ∈ Chapter3.HStar (T : Subgroup G) M, H ≤ Mc ∧
      Nonempty ((H ⧸ pCore 2 H) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  have hout : Chapter3.HasMaximalOutside T M := by
    obtain ⟨L, hL, K, hK, hne⟩ := (Set.one_lt_ncard_iff_nontrivial_and_finite.mp h.many).1
    by_cases hLM : L = M
    · exact Chapter3.hasMaximalOutside_of_two_distinct h.maximal.1.1 hK.1 h.maximal.1.2
        hK.2 (fun he => hne (hLM.trans he.symm))
    · exact Chapter3.hasMaximalOutside_of_two_distinct h.maximal.1.1 hL.1 h.maximal.1.2 hL.2 hLM
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  exact ⟨H, hH, (source_centralizing_HStar_le_seed_centralizer h.ambient T h.maximal
    hH h.centralizing).trans (centralizer_le_partner T h.partner),
    hquotient H hH⟩

omit [Finite G] in
/-- The two-overgroup theorem 15.2.5 makes every HStar member a uniqueness
subgroup. This is the uniqueness assertion used in 15.2.12(3). -/
theorem source_chosen_HStar_unique
    {T : Sylow 2 G} {M Mc H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M, Mc}) :
    ∀ N, IsMaximalTwoLocal N → H ≤ N → N = Mc := by
  intro N hN hHN
  have hm : N ∈ maximalTwoLocalOvergroups (T : Subgroup G) := ⟨hN, hH.1.1.2.trans hHN⟩
  rw [htwo] at hm
  rcases Set.mem_insert_iff.mp hm with he | he
  · exact (hH.1.2 (he ▸ hHN)).elim
  · exact Set.mem_singleton_iff.mp he

/-- The actual normalizer bound in 15.2.12(3), once 15.2.11 constructs
the nontrivial elementary plane and proves its relative H-normality. -/
theorem source_chosen_plane_normalizer
    {T : Sylow 2 G} {M Mc H ZS : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M, Mc})
    [IsElementaryAbelian 2 ZS] (hcard : Nat.card ZS = 4)
    (hHZ : H ≤ normalizer (ZS : Set G)) : normalizer (ZS : Set G) ≤ Mc := by
  apply normalizer_le_of_unique_maximalTwoLocal (source_chosen_HStar_unique hH htwo)
    (IsElementaryAbelian.isPGroup 2 ZS) ?_ hHZ
  intro he
  have hb : Nat.card ZS = 1 := by rw [he]; exact Nat.card_unique
  omega

/-- Original 15.2.14(3) holds for every subgroup of the actual chosen module. -/
theorem ChosenSmallSource.baumann_le_planeCentralizer
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ZS : Subgroup G) (hZV : ZS ≤ V) :
    ChapterB.baumann (T : Subgroup G) ≤ planeCentralizer T ZS := by
  have he := (source_submodule_baumann_control h.ambient T h.maximal
    h.centralizing ZS (hZV.trans h.prepared.le_local)).2.2.1
  rw [he]
  exact inf_le_left

/-- The final deduction in 15.2.14(4) from precisely its two numerical
alternatives. All centers and omega subgroups are embedded in G. -/
theorem source_chosen_plane_eq_omegaCenter
    (T : Sylow 2 G) (ZS : Subgroup G) [IsElementaryAbelian 2 ZS]
    (hZT : ZS ≤ (T : Subgroup G)) (hcard : Nat.card ZS = 4)
    (hcases : (planeCentralizer T ZS = (T : Subgroup G) ∧ centralInvolutions T = ZS) ∨
      (Nat.card (centralInvolutions T) = 2 ∧
        (planeCentralizer T ZS).relIndex (T : Subgroup G) = 2)) :
    ZS = omegaOneCenterAmbient (planeCentralizer T ZS) := by
  let S := planeCentralizer T ZS
  have hZS : ZS ≤ S := le_inf hZT ZS.le_centralizer
  have hZC : ZS ≤ centralizer (S : Set G) := le_centralizer_iff.mp inf_le_right
  rcases hcases with ⟨hS, hZ⟩ | ⟨hZ, hi⟩
  · rw [hS, ← hZ]
    rfl
  · have hf : fixedPlane ZS S = ZS := inf_eq_left.mpr hZC
    let : IsElementaryAbelian 2 (fixedPlane ZS S) := by rw [hf]; infer_instance
    have hh := fixedPlane_eq_centralOmegaIn T ZS S inf_le_left hi hZ
      (hf.le.trans hZS) (by rw [hf]; exact hcard)
    simpa only [hf, centralOmegaIn, omegaOneAmbient, omegaOneCenterAmbient] using hh

/-- The literal 15.2.14(4) consumer: the plane's Sylow containment follows
from the chosen module's normal elementary action, rather than an extra input. -/
theorem ChosenPlaneGeometry.omegaCenter
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hg : ChosenPlaneGeometry h H ZS)
    (hcases : (planeCentralizer T ZS = (T : Subgroup G) ∧ centralInvolutions T = ZS) ∨
      (Nat.card (centralInvolutions T) = 2 ∧
        (planeCentralizer T ZS).relIndex (T : Subgroup G) = 2)) :
    ZS = omegaOneCenterAmbient (planeCentralizer T ZS) := by
  let : IsElementaryAbelian 2 V := h.prepared.elementary
  let : IsElementaryAbelian 2 ZS := IsElementaryAbelian.of_injective
    (inclusion hg.plane_le) (inclusion_injective hg.plane_le)
  let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.prepared.normalized
  let : IsElementaryAbelian 2 (V.subgroupOf M) :=
    IsElementaryAbelian.subgroupOf h.prepared.le_selected
  have hv := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
    (T.subtype h.maximal.1.2)
  have hVT : V ≤ (T : Subgroup G) := by
    have hm := map_mono (f := M.subtype) hv
    simpa only [map_subgroupOf_eq_of_le h.prepared.le_selected, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le h.maximal.1.2] using hm
  exact source_chosen_plane_eq_omegaCenter T ZS (hg.plane_le.trans hVT) hg.plane_card hcases

/-- The intersection consequence actually used in 15.2.12(5) and 15.2.14(5).
Its residual is O^{3'}, with a quotient of order prime to three. -/
theorem source_chosen_intersection_residual_centralizes
    (T : Sylow 2 G) (M Mc H : Subgroup G)
    (heq : partnerSpan H Mc = threePrimeResidual Mc)
    (hcentral : partnerSpan H Mc ≤ centralizer (centralInvolutions T : Set G)) :
    threePrimeResidual (M ⊓ Mc) ≤ M ⊓ centralizer (centralInvolutions T : Set G) := by
  apply le_inf ((map_subtype_le _).trans inf_le_left)
  exact (threePrimeResidual_mono inf_le_right).trans (heq ▸ hcentral)

/-- Assembly into the unchanged shared geometry interface. The remaining
inputs are explicitly 15.2.5, 15.2.8, 15.2.11(2--3) and 15.2.12(5).
This theorem does not construct the offender or prove full support. -/
theorem source_chosen_geometry_of_plane
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    {H ZS : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M, Mc})
    (hquotient : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hfull : V = localModule T M) (hZV : ZS ≤ V) (hcard : Nat.card ZS = 4)
    (hHZ : H ≤ normalizer (ZS : Set G)) : ChosenPlaneGeometry h H ZS := by
  let : IsElementaryAbelian 2 V := h.prepared.elementary
  let : IsElementaryAbelian 2 ZS := IsElementaryAbelian.of_injective
    (inclusion hZV) (inclusion_injective hZV)
  exact ⟨hH, (source_centralizing_HStar_le_seed_centralizer h.ambient T h.maximal
      hH h.centralizing).trans (centralizer_le_partner T h.partner),
    hquotient, hfull, hZV, hcard, hHZ,
    source_chosen_plane_normalizer hH htwo hcard hHZ,
    h.baumann_le_planeCentralizer ZS hZV⟩

end CFSG.Quasithin.Chapter15.Section02

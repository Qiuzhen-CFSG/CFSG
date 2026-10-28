module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialAction
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaOvergroupComparison.Full

/-!
# The original third-local residual in the full extraspecial row

The actual symmetric-three action on the third local module identifies the
literal partner residual modulo its two-core with the cyclic group of order
three. Ordering places this residual in the original intersection and makes
the original action centralizer normalize it. Its image on the original
six-space lies in the extraspecial three-residual, so both original action
kernels are its two-core. That core consequently lies in the original local
core as well. No residual-centralization premise is used.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section02 Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Chapter14.SourcePreliminaries
variable {G : Type*} [Group G] [Finite G]

theorem PreparedChosenModule.extraspecial_third_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    let Y₂ := sourceResidual N Mc
    Y₂ ≤ M ⊓ N ∧ (Y₂.subgroupOf N).Normal ∧ IsPPerfect 2 Y₂ ∧
      Nat.card ((Y₂.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) = 3 ∧
      Y₂.pCoreIn 2 = Y₂ ⊓ centralizer (localModule T N : Set G) ∧
      M ⊓ centralizer (V : Set G) ≤ normalizer (Y₂ : Set G) := by
  let := h.elementary
  let V₁ := localModule T N
  let C := (centralizer (V₁ : Set G)).subgroupOf N
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    ((le_normalizer_conjugateSpanBy _ _).trans (normalizer_le_normalizer_centralizer _))
  let a := actionHom N V₁ (le_normalizer_conjugateSpanBy _ _)
  obtain ⟨e⟩ := h.extraspecial_third_action_symmetricThree hG T hempty
    hM hJ hu hfull hex hN hNM hNMc
  have he : Nonempty ((N ⧸ C) ≃* Equiv.Perm (Fin 3)) := by
    exact ⟨((QuotientGroup.quotientMulEquivOfEq (actionHom_ker N V₁
      (le_normalizer_conjugateSpanBy _ _)).symm).trans
      (QuotientGroup.quotientKerEquivRange a)).trans e⟩
  obtain ⟨hmeet,hne,hcomm⟩ := local_partner_core_inputs hG T hempty hN hu hmany hNMc
  have hs := sourceResidual_splitting N Mc V₁ he.some hmeet hne hcomm
  have hn : ((sourceResidual N Mc).subgroupOf N).Normal := residualY_normal N Mc
  have hn' : N ≤ normalizer (sourceResidual N Mc : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sourceResidual_le N Mc)).mp hn
  have hord := source_ordering_of_centralizing_orderingMaximal hG T hempty
    hM hJ N hN
  refine ⟨ordered_partner_residual_le T hM.1.2 hN.2 hu hord,
    hn,residualY_isPPerfect N Mc,hs.2.1,hs.2.2.2.2.1,?_⟩
  apply le_trans ?_ hn'
  rw [hfull]
  exact ((lemma_A_5_3 hord).2.2 (maximal_local_normalizer_from_source hG T hN)).trans inf_le_left


theorem PreparedChosenModule.extraspecial_third_residual_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    normalizer (sourceResidual N Mc : Set G) = N := by
  obtain ⟨hle,hn,_,hc,hker,_⟩ := h.extraspecial_third_residual hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  let Y := sourceResidual N Mc
  let V₁ := localModule T N
  have hYN : Y ≤ N := sourceResidual_le N Mc
  have hNY : N ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYN).mp hn
  have hne : Y ≠ ⊥ := by
    intro he
    have hb : Y.subgroupOf N = ⊥ := by rw [he,bot_subgroupOf]
    change Nat.card ((Y.subgroupOf N).map _) = 3 at hc
    rw [hb,Subgroup.map_bot,card_bot] at hc
    omega
  have hcore : Y.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hVn : N ≤ normalizer (V₁ : Set G) := le_normalizer_conjugateSpanBy _ _
    let : IsElementaryAbelian 2 V₁ := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hN.1.1,hN.2⟩
    have hcY : ⁅V₁,Y⁆ ≤ Y.pCoreIn 2 := le_pCoreIn_of_normalizes
      ((IsElementaryAbelian.isPGroup 2 V₁).to_le
        (le_normalizer_iff_commutator_le_left.mp (hYN.trans hVn)))
      (le_normalizer_iff_commutator_le_right.mp ((localModule_le T hN.2).trans hNY))
      (normalizer_commutator_ge_right V₁ Y)
    have hcomm : ⁅V₁,Y⁆ = ⊥ := bot_unique (he ▸ hcY)
    have hcent : Y ≤ centralizer (V₁ : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
    have hh : Y = Y.pCoreIn 2 := by rw [hker,inf_eq_left.mpr hcent]
    exact hne (hh.trans he)
  exact normalizer_eq_of_nontrivial_core N Y (Y.pCoreIn 2) hYN hN.1 hn hcore le_rfl

/-- The original residual has the same two-core kernel on V(M) and V(N).
Its original action image lies in the extraspecial three-residual. -/
theorem PreparedChosenModule.extraspecial_third_residual_original_kernel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    let Y₂ := sourceResidual N Mc
    Y₂ ⊓ centralizer (V : Set G) = Y₂.pCoreIn 2 ∧
      Nonempty ((Y₂ ⧸ pCore 2 Y₂) ≃* Multiplicative (ZMod 3)) := by
  let := h.elementary
  obtain ⟨hle,hn,hp,hc,hker,_⟩ := h.extraspecial_third_residual hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  let Y := sourceResidual N Mc
  let f : M →* internalActionImage M V h.normalized :=
    (actionHom M V h.normalized).rangeRestrict
  let a := f.comp (inclusion (hle.trans inf_le_left))
  let D := internalActionImage M V h.normalized
  have himage : a.range ≤ pResidual 2 D := by
    have hh := map_pResidual_le 2 a
    rw [(pResidual_eq_top_iff 2 Y).mpr hp,←MonoidHom.range_eq_map] at hh
    exact hh
  have hcard : Nat.card (pResidual 2 D) = 27 := by
    obtain ⟨_,_,_,_,hc,_,_,_⟩ := hex
    exact hc
  have him3 : IsPGroup 3 a.range :=
    (IsPGroup.of_card (p := 3) (n := 3) hcard).to_le himage
  have hbot : (pCore 2 Y).map a = ⊥ := by
    have h3 : IsPGroup 3 ((pCore 2 Y).map a) := him3.to_le (map_le_range _ _)
    exact disjoint_self.mp (IsPGroup.disjoint_of_ne 2 3 (by decide) _ _
      (pCore_isPGroup.map a) h3)
  have hQc : Y.pCoreIn 2 ≤ centralizer (V : Set G) := by
    rintro x ⟨y,hy,rfl⟩
    have hh : a y = 1 := (Subgroup.map_eq_bot_iff _).mp hbot hy
    have hz : inclusion (hle.trans inf_le_left) y ∈ (actionHom M V h.normalized).ker :=
      congrArg Subtype.val hh
    rwa [actionHom_ker] at hz
  have hord := source_ordering_of_centralizing_orderingMaximal hG T hempty
    hM hJ N hN
  have hcentral : M ⊓ centralizer (V : Set G) ≤
      N ⊓ centralizer (localModule T N : Set G) := by
    rw [hfull]
    exact (lemma_A_5_3 hord).2.2 (maximal_local_normalizer_from_source hG T hN)
  refine ⟨le_antisymm ?_ (le_inf (pCoreIn_le 2 _) hQc),?_⟩
  · intro y hy
    rw [hker]
    exact ⟨hy.1,(hcentral ⟨(hle hy.1).1,hy.2⟩).2⟩
  · let A := Y.subgroupOf N
    let : A.Normal := hn
    let j : A ≃* Y := subgroupOfEquivOfLe (hle.trans inf_le_right)
    let k := QuotientGroup.congr (pCore 2 A) (pCore 2 Y) j (pCore_map_iso 2 j)
    let e : A.map (QuotientGroup.mk' (pCore 2 N)) ≃* Multiplicative (ZMod 3) :=
      mulEquivOfPrimeCardEq hc (by simp)
    exact ⟨k.symm.trans ((coreQuotientEquivImage 2 A).trans e)⟩


/-- The third residual's two-core lies in the original selected local's
 two-core: its normalizer contains the normal action centralizer. -/
theorem PreparedChosenModule.extraspecial_third_residual_twoCore_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    (sourceResidual N Mc).pCoreIn 2 ≤ M.pCoreIn 2 := by
  obtain ⟨hle,_,_,_,_,hCY⟩ :=
    h.extraspecial_third_residual hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  obtain ⟨hker,_⟩ :=
    h.extraspecial_third_residual_original_kernel hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  let Y := sourceResidual N Mc
  let C := M ⊓ centralizer (V : Set G)
  have hQC : Y.pCoreIn 2 ≤ C := le_inf
    ((pCoreIn_le 2 Y).trans (hle.trans inf_le_left)) (hker.symm.le.trans inf_le_right)
  have hCQ : C ≤ normalizer (Y.pCoreIn 2 : Set G) :=
    hCY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hMC : M ≤ normalizer (C : Set G) :=
    (le_inf M.le_normalizer (h.normalized.trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  exact (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Y) hQC hCQ).trans
    (pCoreIn_mono_of_normalizes inf_le_left hMC)

/-- The literal third residual has order-three image modulo the original
local two-core, with precisely its own two-core as the kernel. -/
theorem PreparedChosenModule.extraspecial_third_residual_star_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    let Y₂ := sourceResidual N Mc
    Y₂ ⊓ M.pCoreIn 2 = Y₂.pCoreIn 2 ∧
      Nat.card ((Y₂.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))) = 3 := by
  obtain ⟨hle,_,_,_,_,_⟩ :=
    h.extraspecial_third_residual hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  obtain ⟨_,⟨e⟩⟩ :=
    h.extraspecial_third_residual_original_kernel hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  have hQ := h.extraspecial_third_residual_twoCore_le
    hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  let Y := sourceResidual N Mc
  have hYM : Y ≤ M := hle.trans inf_le_left
  refine ⟨le_antisymm (inf_pCoreIn_le_of_le 2 hYM) (le_inf (pCoreIn_le 2 Y) hQ),?_⟩
  let q := QuotientGroup.mk' (pCore 2 M)
  let a := q.comp (inclusion hYM)
  have hk : a.ker = pCore 2 Y := by
    apply le_antisymm
    · have hp : IsPGroup 2 a.ker := by
        change IsPGroup 2 (q.comp (inclusion hYM)).ker
        rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
        exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hYM)
      exact le_sSup ⟨inferInstance,hp⟩
    · intro y hy
      change q (inclusion hYM y) = 1
      apply (QuotientGroup.eq_one_iff _).mpr
      obtain ⟨m,hm,he⟩ := hQ (mem_map_of_mem Y.subtype hy)
      have he' : inclusion hYM y = m := Subtype.ext he.symm
      rwa [he']
  let eqv := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange a)
  have hc : Nat.card a.range = 3 := (Nat.card_congr eqv.toEquiv).symm.trans
    ((Nat.card_congr e.toEquiv).trans (by simp))
  simpa only [a,MonoidHom.range_comp,inclusion_range] using hc

/-- The original intersection core centralizes the third residual modulo
O₂(M). Both normalizations first put the commutator inside O₂(Y₂). -/
theorem PreparedChosenModule.extraspecial_third_residual_intersection_core_commutator
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    ⁅(M ⊓ N).pCoreIn 2,sourceResidual N Mc⁆ ≤ M.pCoreIn 2 := by
  obtain ⟨hle,hn,_,_,_,_⟩ :=
    h.extraspecial_third_residual hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  have hQ := h.extraspecial_third_residual_twoCore_le
    hG T hempty hM hmany hJ hu hfull hex hN hNM hNMc
  let Y := sourceResidual N Mc
  let R := (M ⊓ N).pCoreIn 2
  have hNY : N ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sourceResidual_le N Mc)).mp hn
  have hRY : R ≤ normalizer (Y : Set G) :=
    ((pCoreIn_le 2 _).trans inf_le_right).trans hNY
  have hYR : Y ≤ normalizer (R : Set G) := hle.trans
    ((M ⊓ N).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (M ⊓ N) (pCore 2 (M ⊓ N : Subgroup G))))
  exact ((le_inf (le_normalizer_iff_commutator_le_right.mp hRY)
    (le_normalizer_iff_commutator_le_left.mp hYR)).trans (inf_pCoreIn_le_of_le 2 hle)).trans hQ

end CFSG.Quasithin.Chapter15.Section01

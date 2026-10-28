module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SourceSmallParabolic
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.OmegaThirdAction
public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.ResidualSplitting
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic
public import Theory.GroupTheory.PResidual.ConjugateSpanSupplement
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.ExtraspecialInvolution
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.PCoreCommutator

/-!
# Maximal-overgroup comparison for the full chosen Omega module

Suppose N is a third maximal two-local above T. Ordering places the literal
residual Y₂=O²(⟨O₂(N∩Mc)^N⟩) inside M∩N. The actual S₃ action of N and
source core growth identify its star image with C₃ and its ambient normalizer
with N. Ordering also identifies its kernel on the original V(M) with O₂(Y₂).

A cubic complement X generates Y₂ under C_M(V). Any abelian Sylow three-group
of M containing X therefore normalizes Y₂ and lies in M∩N, contradicting the
intersection index three. This excludes the elementary-nine and cyclic rows.
In the extraspecial row, the intersection core centralizes the star action
kernel, so its nonidentity involution inverts the whole residual image. But
it is central in the order-twelve intersection image, which contains a cubic
element. This final contradiction proves M(T)={M,Mc} when V=V(M).

The proper chosen support remains a separate branch of this same source-family
owner, qt-e-152-small-parabolic. No proper-support conclusion is asserted here.
Source: Aschbacher--Smith 15.2.5, printed pp.1107--1108.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Chapter14.SourcePreliminaries
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem ordered_partner_residual_le
    (T : Sylow 2 G) {M N Mc : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hTN : (T : Subgroup G) ≤ N)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hord : OrderingLE T N M) : sourceResidual N Mc ≤ M ⊓ N := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  let R := (N ⊓ Mc).pCoreIn 2
  have hRT : R ≤ (T : Subgroup G) := intersectionCore_le_sylow N Mc T hTN hTMc
  have hRN : N ⊓ Mc ≤ normalizer (R : Set G) :=
    (N ⊓ Mc).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (N ⊓ Mc) (pCore 2 (N ⊓ Mc : Subgroup G)))
  have hspan : conjugateSpanBy R N ≤ M := by
    apply (closure_le _).mpr
    rintro x ⟨n,hn,r,hr,rfl⟩
    obtain ⟨a,ha,c,hc,rfl⟩ := hord n hn
    have hcR : c * r * c⁻¹ ∈ R := le_normalizer_iff.mp hRN c
      ⟨hc.1,localModule_centralizer_le_partner T N hu hc.2⟩ r hr
    have he : (a*c)*r*(a*c)⁻¹ = a*(c*r*c⁻¹)*a⁻¹ := by group
    rw [he]
    exact M.mul_mem (M.mul_mem ha.2 (hTM (hRT hcR))) (M.inv_mem ha.2)
  have hRle : R ≤ N := (pCoreIn_le 2 _).trans inf_le_left
  have hnormal : (normalClosure (R.subgroupOf N : Set N)).map N.subtype =
      conjugateSpanBy R N := by
    rw [normalClosure_subgroupOf_eq_conjugateSpanBy R N hRle,
      map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hRle)]
  refine le_inf ?_ (sourceResidual_le N Mc)
  exact (map_mono (f := N.subtype) (map_subtype_le _)).trans (hnormal ▸ hspan)

theorem local_partner_core_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {N Mc : Subgroup G} (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) (hne : N ≠ Mc) :
    (N ⊓ Mc).pCoreIn 2 ⊓ centralizer (localModule T N : Set G) = N.pCoreIn 2 ∧
      ¬ (N ⊓ Mc).pCoreIn 2 ≤ centralizer (localModule T N : Set G) ∧
      ⁅N ⊓ centralizer (localModule T N : Set G),(N ⊓ Mc).pCoreIn 2⁆ ≤ N.pCoreIn 2 := by
  let V := localModule T N
  let C := (centralizer (V : Set G)).subgroupOf N
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    ((le_normalizer_conjugateSpanBy _ _).trans (normalizer_le_normalizer_centralizer _))
  have hVM : V ≤ N := localModule_le T hN.2
  have hred := localModule_reduced_from_source hG T ⟨Chapter1.mem_H_of_isTwoLocal hN.1.1,hN.2⟩
  have hQK : pCore 2 N ≤ C := by
    have hi := le_centralizer_iff.mp hred.le_centralizer_pCore
    intro x hx v hv
    exact congrArg N.subtype (hi hx ⟨v,hVM hv⟩ hv)
  have hCI : C.map N.subtype ≤ N ⊓ Mc := by
    rw [show C = (centralizer (V : Set G)).subgroupOf N from rfl,subgroupOf_map_subtype]
    exact le_inf inf_le_right (inf_le_left.trans (localModule_centralizer_le_partner T N hu))
  have hCcore : C.pCoreIn 2 = pCore 2 N := by
    rw [pCoreIn,pCore_eq_comap_of_normal,map_comap_eq,range_subtype,inf_eq_right.mpr hQK]
  have hQR : N.pCoreIn 2 ≤ (N ⊓ Mc).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 N) ((map_mono hQK).trans hCI)
      (inf_le_left.trans (N.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image N (pCore 2 N))))
  have hQC : N.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (map_mono hQK).trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)
  have hmeet : (N ⊓ Mc).pCoreIn 2 ⊓ centralizer (V : Set G) = N.pCoreIn 2 := by
    apply le_antisymm ?_ (le_inf hQR hQC)
    have hi := inf_pCoreIn_le_of_le 2 hCI
    rw [←map_pCoreIn_of_injective 2 C N.subtype N.subtype_injective,hCcore] at hi
    apply le_trans ?_ hi
    refine le_inf ?_ inf_le_left
    rw [show C = (centralizer (V : Set G)).subgroupOf N from rfl,subgroupOf_map_subtype]
    exact le_inf inf_le_right (inf_le_left.trans ((pCoreIn_le 2 _).trans inf_le_left))
  refine ⟨hmeet,?_,?_⟩
  · intro hc
    have hMc : Mc ∈ maximalTwoLocalOvergroups
        (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
    have hTMc : (T : Subgroup G) ≤ Mc := by
      intro t ht
      exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
    apply intersection_core_ne_local_core_from_source hG T hempty hN ⟨hMc.1,hTMc⟩ hu hmany hne
    rwa [inf_eq_left.mpr hc] at hmeet
  · let H := (N ⊓ Mc).subgroupOf N
    have hCH : C ≤ H := fun x hx => hCI (mem_map_of_mem N.subtype hx)
    have he : H.pCoreIn 2 = ((N ⊓ Mc).pCoreIn 2).subgroupOf N := by
      rw [pCoreIn_subgroupOf 2 (N ⊓ Mc) N inf_le_left]
    have hh := map_mono (f := N.subtype) (commutator_pCoreIn_le_of_normal (p := 2) C H hCH)
    rw [map_commutator,he,map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans inf_le_left),
      show C.map N.subtype = N ⊓ centralizer (V : Set G) by
        rw [subgroupOf_map_subtype,inf_comm]] at hh
    exact hh

theorem ChosenSmallSource.omega_full_third_residual
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    let Y₂ := sourceResidual N Mc
    Y₂ ≤ M ⊓ N ∧ (Y₂.subgroupOf N).Normal ∧ IsPPerfect 2 Y₂ ∧
      Nat.card ((Y₂.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) = 3 ∧
      Y₂.pCoreIn 2 = Y₂ ⊓ centralizer (localModule T N : Set G) ∧
      M ⊓ centralizer (V : Set G) ≤ normalizer (Y₂ : Set G) := by
  let := h.prepared.elementary
  let V₁ := localModule T N
  let C := (centralizer (V₁ : Set G)).subgroupOf N
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    ((le_normalizer_conjugateSpanBy _ _).trans (normalizer_le_normalizer_centralizer _))
  let a := actionHom N V₁ (le_normalizer_conjugateSpanBy _ _)
  obtain ⟨e⟩ := h.prepared.omega_full_third_action_symmetricThree h.ambient T h.empty
    h.maximal h.centralizing h.partner ho hfull hN hNM hNMc
  have he : Nonempty ((N ⧸ C) ≃* Equiv.Perm (Fin 3)) := by
    exact ⟨((QuotientGroup.quotientMulEquivOfEq (actionHom_ker N V₁
      (le_normalizer_conjugateSpanBy _ _)).symm).trans
      (QuotientGroup.quotientKerEquivRange a)).trans e⟩
  obtain ⟨hmeet,hne,hcomm⟩ := local_partner_core_inputs h.ambient T h.empty hN h.partner h.many hNMc
  have hs := sourceResidual_splitting N Mc V₁ he.some hmeet hne hcomm
  have hn : ((sourceResidual N Mc).subgroupOf N).Normal := residualY_normal N Mc
  have hn' : N ≤ normalizer (sourceResidual N Mc : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sourceResidual_le N Mc)).mp hn
  have hord := source_ordering_of_centralizing_orderingMaximal h.ambient T h.empty
    h.maximal h.centralizing N hN
  refine ⟨ordered_partner_residual_le T h.maximal.1.2 hN.2 h.partner hord,
    hn,residualY_isPPerfect N Mc,hs.2.1,hs.2.2.2.2.1,?_⟩
  apply le_trans ?_ hn'
  rw [hfull]
  exact ((lemma_A_5_3 hord).2.2 (maximal_local_normalizer_from_source h.ambient T hN)).trans inf_le_left


theorem ChosenSmallSource.omega_full_third_residual_normalizer
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    normalizer (sourceResidual N Mc : Set G) = N := by
  obtain ⟨hle,hn,_,hc,hker,_⟩ := h.omega_full_third_residual ho hfull hN hNM hNMc
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
    let : IsElementaryAbelian 2 V₁ := localModule_elementary_from_source h.ambient T
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

/-- The third residual is faithful modulo its two-core on the original V(M),
not only on V(N). Its image cannot retain two-torsion inside O²(S₃ × S₃). -/
theorem ChosenSmallSource.omega_full_third_residual_original_kernel
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    let Y₂ := sourceResidual N Mc
    Y₂ ⊓ centralizer (V : Set G) = Y₂.pCoreIn 2 ∧
      Nonempty ((Y₂ ⧸ pCore 2 Y₂) ≃* Multiplicative (ZMod 3)) := by
  let := h.prepared.elementary
  obtain ⟨hle,hn,hp,hc,hker,_⟩ := h.omega_full_third_residual ho hfull hN hNM hNMc
  let Y := sourceResidual N Mc
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  let a := f.comp (inclusion (hle.trans inf_le_left))
  let D := (actionHom M V h.prepared.normalized).range
  have himage : a.range ≤ pResidual 2 D := by
    have hh := map_pResidual_le 2 a
    rw [(pResidual_eq_top_iff 2 Y).mpr hp,←MonoidHom.range_eq_map] at hh
    exact hh
  have hcard : Nat.card (pResidual 2 D) = 9 := by
    have hh := congrArg (fun K : Subgroup SymmetricThreeProduct.G => Nat.card K)
      (map_pResidual 2 ho.2.2.2.1.some)
    rw [card_map_of_injective ho.2.2.2.1.some.injective,
      SymmetricThreeProductResidual.residual_card] at hh
    exact hh
  have him3 : IsPGroup 3 a.range :=
    (IsPGroup.of_card (p := 3) (n := 2) hcard).to_le himage
  have hbot : (pCore 2 Y).map a = ⊥ := by
    have h3 : IsPGroup 3 ((pCore 2 Y).map a) := him3.to_le (map_le_range _ _)
    exact disjoint_self.mp (IsPGroup.disjoint_of_ne 2 3 (by decide) _ _
      (pCore_isPGroup.map a) h3)
  have hQc : Y.pCoreIn 2 ≤ centralizer (V : Set G) := by
    rintro x ⟨y,hy,rfl⟩
    have hh : a y = 1 := (Subgroup.map_eq_bot_iff _).mp hbot hy
    have hz : inclusion (hle.trans inf_le_left) y ∈ (actionHom M V h.prepared.normalized).ker :=
      congrArg Subtype.val hh
    rwa [actionHom_ker] at hz
  have hord := source_ordering_of_centralizing_orderingMaximal h.ambient T h.empty
    h.maximal h.centralizing N hN
  have hcentral : M ⊓ centralizer (V : Set G) ≤
      N ⊓ centralizer (localModule T N : Set G) := by
    rw [hfull]
    exact (lemma_A_5_3 hord).2.2 (maximal_local_normalizer_from_source h.ambient T hN)
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


/-- A third maximal local in the full Omega row forces a nonabelian Sylow
three-subgroup of the original M. This is the final Sylow comparison on p.1108. -/
theorem ChosenSmallSource.omega_full_third_nonabelian_threeSylow
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    ∃ P : Sylow 3 M, ¬ IsMulCommutative P := by
  let := h.prepared.elementary
  obtain ⟨hle,hn,hp,_,_,hCY⟩ := h.omega_full_third_residual ho hfull hN hNM hNMc
  obtain ⟨hker,⟨e⟩⟩ := h.omega_full_third_residual_original_kernel ho hfull hN hNM hNMc
  have hnorm := h.omega_full_third_residual_normalizer ho hfull hN hNM hNMc
  let Y := sourceResidual N Mc
  let C := M ⊓ centralizer (V : Set G)
  have hYM : Y ≤ M := hle.trans inf_le_left
  have hc : Nat.card (Y ⧸ pCore 2 Y) = 3 := (Nat.card_congr e.toEquiv).trans (by simp)
  obtain ⟨x,hx,hgen⟩ := exists_prime_order_sup_pCore_eq_top (G := Y) (by decide : Nat.Coprime 2 3) hc
  let X := zpowers (x : G)
  have hXQ : X ⊔ Y.pCoreIn 2 = Y := by
    have hh := congrArg (map Y.subtype) hgen
    simpa only [X,pCoreIn,Subgroup.map_sup,MonoidHom.map_zpowers,subtype_apply,
      ←MonoidHom.range_eq_map,range_subtype] using hh
  have hXC : conjugateSpanBy X C = Y := conjugateSpan_eq_of_pPerfect_supplement
    Y X C (Y.pCoreIn 2) hp (isPGroup_pCoreIn 2 Y) hXQ
      (le_inf ((pCoreIn_le 2 Y).trans hYM) (hker.symm.le.trans inf_le_right)) hCY
  let xM : M := inclusion hYM x
  have hxM : orderOf xM = 3 := (orderOf_injective (inclusion hYM) (inclusion_injective hYM) x).trans hx
  have hX3 : IsPGroup 3 (zpowers xM) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers,pow_one] using hxM)
  obtain ⟨P,hXP⟩ := hX3.exists_le_sylow
  refine ⟨P,?_⟩
  intro hab
  let : IsMulCommutative P := hab
  let P₀ := (P : Subgroup M).map M.subtype
  have hPX : P₀ ≤ centralizer (X : Set G) := by
    rintro _ ⟨p,hpP,rfl⟩ z hz
    have hXmap : (zpowers xM).map M.subtype = X := by rw [MonoidHom.map_zpowers]; rfl
    have hzmap : z ∈ (zpowers xM).map M.subtype := by rw [hXmap]; exact hz
    obtain ⟨w,hw,he⟩ := hzmap
    rw [←he]
    exact congrArg M.subtype (congrArg (P : Subgroup M).subtype
      (mul_comm (⟨w,hXP hw⟩ : P) ⟨p,hpP⟩))
  have hMC : M ≤ normalizer (C : Set G) :=
    (le_inf M.le_normalizer (h.prepared.normalized.trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hPY : P₀ ≤ normalizer (Y : Set G) := by
    rw [←hXC]
    exact normalizes_conjugateSpanBy X C P₀ (hPX.trans (Subgroup.centralizer_le_normalizer _))
      ((map_subtype_le _).trans hMC)
  rw [hnorm] at hPY
  let H := (M ⊓ N).subgroupOf M
  have hPH : (P : Subgroup M) ≤ H := by
    intro p hpP
    exact ⟨p.property,hPY (mem_map_of_mem M.subtype hpP)⟩
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  let A := H.map f
  have hord := source_ordering_of_centralizing_orderingMaximal h.ambient T h.empty
    h.maximal h.centralizing N hN
  have hCH : f.ker ≤ H := by
    intro m hm
    have hh : m ∈ (actionHom M V h.prepared.normalized).ker := congrArg Subtype.val hm
    rw [actionHom_ker] at hh
    have hCN : M ⊓ centralizer (V : Set G) ≤ N := by
      rw [hfull]
      exact ((lemma_A_5_3 hord).2.2 (maximal_local_normalizer_from_source h.ambient T hN)).trans inf_le_left
    exact ⟨m.property,hCN ⟨m.property,hh⟩⟩
  have hAc : Nat.card A = 12 :=
    (h.prepared.omega_third_maximal_intersection h.ambient T h.empty h.maximal
      h.centralizing h.partner h.many ho.2.2.2.1.some hN hNM hNMc).2.1
  have hDc : Nat.card (actionHom M V h.prepared.normalized).range = 36 := by
    exact (Nat.card_congr ho.2.2.2.1.some.toEquiv).trans (by
      simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial])
  have hHi : H.index = 3 := by
    have hh := A.index_mul_card
    rw [hAc,hDc] at hh
    have hi : A.index = H.index := H.index_map_eq (actionHom M V h.prepared.normalized).rangeRestrict_surjective hCH
    omega
  have hd := index_dvd_of_le hPH
  rw [hHi] at hd
  exact P.not_dvd_index hd


private theorem threeSylow_commutative_of_coprime_kernel
    {M : Subgroup G} {D : Type*} [Group D] [Finite D] (f : M →* D)
    (hf : Function.Surjective f) (hd : Nat.card D = 36)
    (hc : Nat.Coprime 3 (Nat.card f.ker)) (P : Sylow 3 M) : IsMulCommutative P := by
  let Q := P.mapSurjective hf
  have hQc : Nat.card Q = 9 := by rw [Q.card_eq_multiplicity,hd]; decide +kernel
  have hi := injective_comp_subtype_of_coprime_ker f hc (P : Subgroup M) P.isPGroup'
  let e : P ≃* Q := MulEquiv.ofBijective (f.subgroupMap (P : Subgroup M))
    ⟨fun x y h => hi (congrArg Subtype.val h),f.subgroupMap_surjective _⟩
  have hPc : Nat.card P = 3 ^ 2 := (Nat.card_congr e.toEquiv).trans hQc
  exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hPc

/-- The elementary-nine and cyclic Omega rows cannot admit a third local
when the chosen module is full. Thus any surviving third local forces the
literal extraspecial star residual of order 27. -/
theorem ChosenSmallSource.omega_full_third_forces_extraspecial
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    letI := h.prepared.elementary
    let P := (h.residual.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))
    Nat.card P = 27 ∧ IsExtraspecial 3 P := by
  let := h.prepared.elementary
  obtain ⟨P,hP⟩ := h.omega_full_third_nonabelian_threeSylow ho hfull hN hNM hNMc
  have hs := source_omega_chosen_residual_complete h.ambient T h.empty h.maximal
    h.centralizing h.partner h.many h.prepared ho
  rcases hs.alternatives with ⟨_,_,_,_,_,_,hcop⟩ | ⟨_,hc,hex,_⟩ | ⟨_,_,_,_,_,_,_,_,hcyc⟩
  · exfalso
    apply hP
    let f := (actionHom M V h.prepared.normalized).rangeRestrict
    have hker : f.ker.map M.subtype = M ⊓ centralizer (V : Set G) := by
      rw [MonoidHom.ker_rangeRestrict,actionHom_ker,subgroupOf_map_subtype,inf_comm]
    have hcop' : Nat.Coprime 3 (Nat.card f.ker) := by
      rwa [←hker,card_map_of_injective M.subtype_injective] at hcop
    have hDc : Nat.card (actionHom M V h.prepared.normalized).range = 36 :=
      (Nat.card_congr ho.2.2.2.1.some.toEquiv).trans (by
        simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial])
    exact threeSylow_commutative_of_coprime_kernel f
      (actionHom M V h.prepared.normalized).rangeRestrict_surjective hDc hcop' P
  · exact ⟨hc,hex⟩
  · exfalso
    apply hP
    obtain ⟨n,_,⟨e⟩⟩ := hcyc P
    exact ⟨⟨fun a b => e.injective (by simp only [map_mul,mul_comm])⟩⟩


/-- Full-module Omega comparison: a third maximal local cannot occur. -/
theorem ChosenSmallSource.omega_full_no_third_maximal
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    False := by
  let := h.prepared.elementary
  obtain ⟨hc27,hex⟩ := h.omega_full_third_forces_extraspecial ho hfull hN hNM hNMc
  let Y := h.residual.subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  let P := Y.map q
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  let g := omegaStarActor h.prepared.normalized ho
  let R₀ := ((M ⊓ N).pCoreIn 2).subgroupOf M
  let R := R₀.map f
  let H := (M ⊓ N).subgroupOf M
  let A := H.map f
  let : Y.Normal := source_omega_lemma_15_2_3_2 T h.maximal.1.2 h.prepared.normalized ho
  let : P.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : IsExtraspecial 3 P := hex
  have hs := source_omega_chosen_residual_complete h.ambient T h.empty h.maximal
    h.centralizing h.partner h.many h.prepared ho
  have hfullY : Y.map f = pResidual 2 (actionHom M V h.prepared.normalized).range := by
    rcases hs.alternatives with ⟨_,_,hc9,_⟩ | ⟨hf,_⟩ | ⟨_,_,hc3,_⟩
    · have hh : (27:ℕ)=9 := hc27.symm.trans hc9
      omega
    · exact hf
    · have hh : (27:ℕ)=3 := hc27.symm.trans hc3
      omega
  have hnine : Nat.card (Y.map f) = 9 := by
    rw [hfullY]
    have hh := congrArg (fun K : Subgroup SymmetricThreeProduct.G => Nat.card K)
      (map_pResidual 2 ho.2.2.2.1.some)
    rw [card_map_of_injective ho.2.2.2.1.some.injective,
      SymmetricThreeProductResidual.residual_card] at hh
    exact hh
  have him : P.map g = pResidual 2 (actionHom M V h.prepared.normalized).range := by
    rw [omegaStarActor_map]
    exact hfullY
  have hk : (g.domRestrict P).ker = center P :=
    source_omega_extraspecial_star_kernel T h.maximal.1.2 h.partner h.prepared ho hnine hex
  have hgC : g.ker ≤ centralizer (P : Set _) :=
    source_omega_star_kernel_centralizes T h.maximal.1.2 h.partner h.prepared ho
  obtain ⟨_,hAc,hReq,hRc⟩ := h.prepared.omega_full_third_maximal_core h.ambient T h.empty
    h.maximal h.centralizing h.partner h.many ho hfull hN hNM hNMc
  have hrC : (R₀.map q) ≤ centralizer (g.ker : Set _) := by
    have hord := source_ordering_of_centralizing_orderingMaximal h.ambient T h.empty
      h.maximal h.centralizing N hN
    have hCH : f.ker ≤ H := by
      intro m hm
      have hh : m ∈ (actionHom M V h.prepared.normalized).ker := congrArg Subtype.val hm
      rw [actionHom_ker] at hh
      have hCN : M ⊓ centralizer (V : Set G) ≤ N := by
        rw [hfull]
        exact ((lemma_A_5_3 hord).2.2 (maximal_local_normalizer_from_source h.ambient T hN)).trans inf_le_left
      exact ⟨m.property,hCN ⟨m.property,hh⟩⟩
    have hcomm : ⁅f.ker,R₀⁆ ≤ pCore 2 M := by
      have he : H.pCoreIn 2 = R₀ := pCoreIn_subgroupOf 2 (M ⊓ N) M inf_le_left
      rw [←he]
      exact commutator_pCoreIn_le_of_normal f.ker H hCH
    have hkg : g.ker = f.ker.map q := QuotientGroup.ker_lift _ _ _
    rw [hkg]
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hcomm
  change Nat.card R = 2 at hRc
  change R = A.pCoreIn 2 at hReq
  change Nat.card A = 12 at hAc
  let : Nontrivial R := Finite.one_lt_card_iff_nontrivial.mp (by rw [hRc]; decide)
  obtain ⟨r,hrne⟩ := exists_ne (1 : R)
  have hrne' : (r : (actionHom M V h.prepared.normalized).range) ≠ 1 :=
    fun he => hrne (Subtype.ext he)
  obtain ⟨r₀,hr₀,he⟩ := r.property
  have hrne : f r₀ ≠ 1 := by rwa [he]

  have hsq : (g (q r₀))^2=1 := by
    have hh := pow_card_eq_one' (x := (⟨f r₀,mem_map_of_mem f hr₀⟩ : R))
    rw [hRc] at hh
    exact congrArg Subtype.val hh
  have hinv := SymmetricThreeProductResidual.central_kernel_involution_inverts_extraspecial_image
    g ho.2.2.2.1.some P hc27 him hk hgC (q r₀) hsq hrne
      (hrC (mem_map_of_mem q hr₀))
  have hAR : A ≤ normalizer (R : Set _) := by
    rw [hReq]
    exact A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hAC : A ≤ centralizer (R : Set _) :=
    hAR.trans (normalizer_le_centralizer_of_card_two R hRc)
  have hd : 3 ∣ Nat.card A := by rw [hAc]; decide
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 hd
  have hpow : (a : (actionHom M V h.prepared.normalized).range)^3=1 :=
    congrArg A.subtype (ha ▸ pow_orderOf_eq_one a)
  have hares : (a : (actionHom M V h.prepared.normalized).range) ∈
      pResidual 2 (actionHom M V h.prepared.normalized).range :=
    mem_pResidual_of_orderOf_coprime ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hpow))
  have hv := hinv a hares
  have hc := hAC a.property (f r₀) (mem_map_of_mem f hr₀)
  have heq : (a : (actionHom M V h.prepared.normalized).range) = (a : (actionHom M V h.prepared.normalized).range)⁻¹ := by
    calc
      _ = f r₀ * (a : (actionHom M V h.prepared.normalized).range) * (f r₀)⁻¹ := by
        rw [hc,mul_assoc,mul_inv_cancel,mul_one]
      _ = _ := hv
  have hsquare : (a : (actionHom M V h.prepared.normalized).range)^2=1 := by
    calc
      _ = (a : (actionHom M V h.prepared.normalized).range) * a := pow_two _
      _ = (a : (actionHom M V h.prepared.normalized).range)⁻¹ * a := congrArg (fun z : (actionHom M V h.prepared.normalized).range => z * (a : (actionHom M V h.prepared.normalized).range)) heq
      _ = 1 := inv_mul_cancel _
  have htwo := orderOf_dvd_of_pow_eq_one hsquare
  rw [A.orderOf_coe,ha] at htwo
  norm_num at htwo


/-- Original 15.2.5 in the full chosen Omega case. -/
theorem ChosenSmallSource.maximal_overgroups_of_full_omega
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized))
    (hfull : V = localModule T M) :
    maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc} := by
  classical
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := h.partner ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  ext N
  constructor
  · intro hN
    by_cases hNM : N = M
    · simp [hNM]
    by_cases hNMc : N = Mc
    · simp [hNMc]
    exact (h.omega_full_no_third_maximal ho hfull hN hNM hNMc).elim
  · intro hN
    rcases Set.mem_insert_iff.mp hN with rfl | hN
    · exact h.maximal.1
    · obtain rfl := Set.mem_singleton_iff.mp hN
      exact ⟨hMc.1,hTMc⟩

end CFSG.Quasithin.Chapter15.Section02

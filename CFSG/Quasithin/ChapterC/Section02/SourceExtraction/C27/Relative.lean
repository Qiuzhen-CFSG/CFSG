module

public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.Offender
/-!
# Original C.2.7(1–2) for a relatively normal component

Work inside the actual local group H to use radical saturation and
characteristic-normalizer control, then carry the two-core, omega-center,
and elementary Thompson subgroup through H's inclusion. The resulting
kernel, reducedness and offenders are expressed in the original star quotient
(KR)/C_KR(Ω₁Z(O₂(KR))), retaining every original subgroup and action.

The quasisimple component survives because otherwise it fixes Ω₁Z(R).
Its central kernel has no extra normal two-subgroup. The actual maximum
elementary subgroups of R then supply a best offender. No component/module
classification or assumed kernel bound enters the proof.

Source: Aschbacher--Smith C.2.7(1–2), pp.145–146, on the normal component
provided in the original 14.7.68 fixed-centralizer argument.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

private theorem source_bounds (h : Input κ H R M K) [(K.subgroupOf H).Normal] :
    (K ⊔ R).pCoreIn 2 ≤ R ∧
    ¬ K.subgroupOf (K ⊔ R) ≤ starKernel K R ∧
    ¬ elementaryAbelianMaxJ R ≤ elementaryAbelianMaxJ ((K ⊔ R).pCoreIn 2) := by
  let KH := K.subgroupOf H
  let RH := R.subgroupOf H
  let MH := M.subgroupOf H
  have hKm : KH.map H.subtype = K := map_subgroupOf_eq_of_le h.component.1
  have hRm : RH.map H.subtype = R := map_subgroupOf_eq_of_le h.setup.radical_le
  have hJm : (KH ⊔ RH).map H.subtype = K ⊔ R := by rw [Subgroup.map_sup,hKm,hRm]
  have hQm : ((KH ⊔ RH).pCoreIn 2).map H.subtype = (K ⊔ R).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,hJm]
  have hQR : (K ⊔ R).pCoreIn 2 ≤ R := by
    rw [←hQm,←hRm]
    exact map_mono (joinCore_le_radical KH RH h.setup.radical)
  have hout : ¬ KH ≤ MH := fun hh => h.outside (by
    have hm := map_mono (f := H.subtype) hh
    rwa [hKm,map_subgroupOf_eq_of_le h.setup.overgroup_le] at hm)
  have hth : ¬ elementaryAbelianMaxJ R ≤ elementaryAbelianMaxJ ((K ⊔ R).pCoreIn 2) := by
    intro hh
    apply thompson_not_le_joinCore KH RH MH h.setup.radical h.setup.characteristic_control hout
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hRm,hQm]
    exact hh
  have hc : centralizer (pCore 2 K : Set K) ≤ pCore 2 K := by
    rw [← h.fitting]
    exact centralizer_generalizedFitting_le K
  have hJc := centralizer_pCore_sup_le 2 K R hc
    (hRm ▸ h.setup.radical.isPGroup.map H.subtype) h.normalizes
  have hOmega : omegaOneCenterAmbient R ≤ (starV K R).map (K ⊔ R : Subgroup G).subtype := by
    intro x hx
    obtain ⟨hxR,hx2,hcent⟩ := (mem_omegaOneCenterAmbient_iff R x).mp hx
    let xJ : (K ⊔ R : Subgroup G) := ⟨x,mem_sup_right hxR⟩
    have hxC : xJ ∈ centralizer (pCore 2 (K ⊔ R : Subgroup G) : Set (K ⊔ R : Subgroup G)) := by
      intro a ha
      exact Subtype.ext (hcent a (hQR (mem_map_of_mem (K ⊔ R : Subgroup G).subtype ha)))
    refine ⟨xJ,?_,rfl⟩
    change xJ ∈ omegaOneCenterAmbient (pCore 2 (K ⊔ R : Subgroup G))
    exact (mem_omegaOneCenterAmbient_iff _ xJ).mpr
      ⟨hJc hxC,Subtype.ext hx2,fun a ha => hxC a ha⟩
  refine ⟨hQR,?_,hth⟩
  intro hfix
  have hKO : K ≤ centralizer (omegaOneCenterAmbient R : Set G) := by
    intro k hk v hv
    obtain ⟨a,ha,rfl⟩ := hOmega hv
    exact congrArg Subtype.val ((hfix (show (⟨k,mem_sup_left hk⟩ : (K ⊔ R : Subgroup G)) ∈
      K.subgroupOf (K ⊔ R) from hk)) a ha)
  have hOm : (omegaOneCenterAmbient RH).map H.subtype = omegaOneCenterAmbient R := by
    rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,hRm]
  have hfixH : KH ≤ centralizer (omegaOneCenterAmbient RH : Set H) := by
    intro k hk v hv
    exact Subtype.ext ((hKO hk) v (hOm ▸ mem_map_of_mem H.subtype hv))
  let C : Subgroup RH := (omega₁ (center RH) (p := 2)).map (center RH).subtype
  let : (omega₁ (center RH) (p := 2)).Characteristic := omega₁_characteristic _
  let : C.Characteristic := inferInstance
  let : Nontrivial RH := (nontrivial_iff_ne_bot RH).mpr h.setup.radical.1
  have hCne : C ≠ ⊥ := omega_center_ne_bot h.setup.radical.isPGroup
  exact hout ((hfixH.trans (Subgroup.centralizer_le_normalizer _)).trans
    ((normalizer_le_characteristicNormalizerClosure RH C hCne).trans h.setup.characteristic_control))


theorem kernel_offender_of_normal_input (h : Input κ H R M K)
    [(K.subgroupOf H).Normal] : KernelConclusion K R ∧ OffenderConclusion K R := by
  obtain ⟨hQR,hmove,hth⟩ := source_bounds h
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  let J := K ⊔ R
  let K₀ := K.subgroupOf J
  let R₀ := R.subgroupOf J
  let V := starV K R
  let q := QuotientGroup.mk' (starKernel K R)
  let e : K₀ ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  let : IsQuasisimple (K₀ ⧸ pCore 2 K₀) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hK : K₀.IsCComponent := h.component.2.subgroupOf_of_le le_sup_left h.join_le
  have hR : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  have hgen : K₀ ⊔ R₀ = ⊤ := by
    rw [← subgroupOf_sup (show K ≤ J from le_sup_left) (show R ≤ J from le_sup_right),subgroupOf_self]
  have hkernel : KernelConclusion K R := by
    have hs := QuasisimpleKernel.normal_kernel_structure K₀ R₀ (starKernel K R)
      hK hR.comap_subtype hgen (core_le_starKernel K R) hmove
    have heC : coreCenterImage K R = K₀.coreCenterIn 2 := by
      apply map_injective J.subtype_injective
      rw [map_coreCenterIn_of_injective 2 K₀ J.subtype J.subtype_injective,
        map_subgroupOf_eq_of_le (show K ≤ J from le_sup_left)]
      rw [coreCenterImage,map_map,coreCenterIn,Subgroup.upperCentralSeriesStep_eq_comap_center]
      rfl
    refine ⟨core_le_starKernel K R,?_,⟨inferInstance,inferInstance,hs.2⟩⟩
    change starKernel K R ≤ pCore 2 J ⊔ coreCenterImage K R
    rw [heC,coreCenterIn,Subgroup.upperCentralSeriesStep_eq_comap_center]
    exact hs.1
  refine ⟨hkernel,?_⟩
  have hcomm : ⁅V,K₀⁆ ≠ ⊥ := by
    rw [commutator_comm,ne_eq,commutator_eq_bot_iff_le_centralizer]
    exact hmove
  have hQR' : pCore 2 J ≤ R₀ := fun x hx => hQR (mem_map_of_mem J.subtype hx)
  obtain ⟨T,hRT⟩ := hR.comap_subtype.exists_le_sylow (P := R₀)
  have hprod : ∀ g : J, ∃ l ∈ K₀, ∃ t ∈ (T : Subgroup J), l*t=g := by
    intro g
    obtain ⟨l,hl,t,ht,he⟩ := mem_sup_of_normal_left.mp (hgen.symm ▸ mem_top g)
    exact ⟨l,hl,t,hRT ht,he⟩
  have hcore := (internalModule_quasisimple_core_structure V q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hkernel.reduced.2.2 T K₀ hK inferInstance hcomm hprod).1
  have hCR : R₀ ⊓ starKernel K R = pCore 2 J := le_antisymm
    ((inf_le_inf_right _ hRT).trans hcore.ge) (le_inf hQR' hkernel.lower)
  have hVR : V ≤ R₀ := (map_subtype_le _).trans hQR'
  have hJ : ¬ elementaryAbelianMaxJ R₀ ≤ starKernel K R := by
    intro hh
    have hle : elementaryAbelianMaxJ R₀ ≤ pCore 2 J := hCR ▸
      le_inf (sSup_le fun _ hA => hA.1) hh
    have he := elementaryAbelianMaxJ_eq_of_intermediate R₀ (pCore 2 J) hle hQR'
    have hm := congrArg (map J.subtype) he
    rw [← elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
      ← elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right)] at hm
    exact hth hm.ge
  have hA : ∃ A, A ∈ elementaryAbelianMaxSubgroups R₀ ∧ ¬ A ≤ starKernel K R := by
    by_contra! hh
    exact hJ (sSup_le hh)
  obtain ⟨A,hA,hne⟩ := hA
  have hb := Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
    V q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) R₀ A hVR hA
    (fun hbot => hne (by
      have hh := (Subgroup.map_eq_bot_iff A).mp hbot
      simpa only [show q.ker = starKernel K R from QuotientGroup.ker_mk' _] using hh))
  have hbest : IsStarBestOffender K R (A.map q) := hb
  exact ⟨hth,⟨A.map q,hbest.offender⟩,⟨A.map q,map_mono hA.1,hbest⟩⟩
end CFSG.Quasithin.ChapterC.C27Source

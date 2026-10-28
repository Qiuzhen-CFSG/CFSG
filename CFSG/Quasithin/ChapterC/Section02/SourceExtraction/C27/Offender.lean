module

public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.Kernel
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupTheory.GeneralizedFitting.InternalModuleResidual.Quasisimple
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.MaximalImages
/-!
# Actual C.2.7 offenders

The normal component source in C.2.7 uses the literal omega-center of O₂(KR).
Characteristic-normalizer control forces nontrivial action; quasisimple kernel
structure and maximum elementary subgroups give the actual source clauses.

Source: Aschbacher--Smith, C.2.7(1–2), printed pp.145–146.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.StarSelection
variable {G : Type*} [Group G] [Finite G]
theorem thompson_not_le_joinCore (K R M : Subgroup G) [K.Normal]
    (hr : IsPRadical 2 R)
    (hcontrol : R.characteristicNormalizerClosure ≤ M) (hout : ¬ K ≤ M) :
    ¬ elementaryAbelianMaxJ R ≤ elementaryAbelianMaxJ ((K ⊔ R).pCoreIn 2) := by
  intro h
  have hQR := joinCore_le_radical K R hr
  have he := elementaryAbelianMaxJ_eq_of_intermediate R ((K ⊔ R).pCoreIn 2)
    (h.trans (sSup_le fun _ hA => hA.1)) hQR
  have hKN : K ≤ normalizer (elementaryAbelianMaxJ R : Set G) := by
    rw [← he]
    exact (le_sup_left.trans (K ⊔ R).le_normalizer).trans
      ((normalizer_le_normalizer_characteristic_image _ (pCore 2 _)).trans
        (normalizer_le_normalizer_elementaryAbelianMaxJ _))
  exact hout (hKN.trans ((normalizer_maxJ_le_characteristicNormalizerClosure R R
    (sSup_le fun _ hA => hA.1) le_rfl
    (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup R hr.isPGroup hr.1)).trans hcontrol))

theorem offender_of_normal_component (K R M : Subgroup G) [K.Normal]
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hr : IsPRadical 2 R)
    (hc : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hcontrol : R.characteristicNormalizerClosure ≤ M) (hout : ¬ K ≤ M) :
    OffenderConclusion K R := by
  let J := K ⊔ R
  let K₀ := K.subgroupOf J
  let R₀ := R.subgroupOf J
  let V := starV K R
  let q := QuotientGroup.mk' (starKernel K R)
  let e : K₀ ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let : IsQuasisimple (K₀ ⧸ pCore 2 K₀) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hkernel := kernel_of_normal_component K R M hK hr hc hcontrol hout
  have hmove := outside_moves_starV K R M hr hc hcontrol hout
  have hcomm : ⁅V,K₀⁆ ≠ ⊥ := by
    rw [commutator_comm,ne_eq,commutator_eq_bot_iff_le_centralizer]
    exact hmove
  have hQR : pCore 2 J ≤ R₀ := fun x hx =>
    joinCore_le_radical K R hr (mem_map_of_mem J.subtype hx)
  obtain ⟨T,hRT⟩ := hr.isPGroup.comap_subtype.exists_le_sylow (P := R₀)
  have hgen : K₀ ⊔ R₀ = ⊤ := by
    rw [← subgroupOf_sup (show K ≤ J from le_sup_left) (show R ≤ J from le_sup_right),subgroupOf_self]
  have hprod : ∀ g : J, ∃ l ∈ K₀, ∃ t ∈ (T : Subgroup J), l*t=g := by
    intro g
    obtain ⟨l,hl,t,ht,he⟩ := mem_sup_of_normal_left.mp (hgen.symm ▸ mem_top g)
    exact ⟨l,hl,t,hRT ht,he⟩
  have hcore := (internalModule_quasisimple_core_structure V q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hkernel.reduced.2.2 T K₀ (hK.subgroupOf (show K ≤ J from le_sup_left))
    inferInstance hcomm hprod).1
  have hCR : R₀ ⊓ starKernel K R = pCore 2 J := le_antisymm
    ((inf_le_inf_right _ hRT).trans hcore.ge) (le_inf hQR hkernel.lower)
  have hVR : V ≤ R₀ := (map_subtype_le _).trans hQR
  have hth := thompson_not_le_joinCore K R M hr hcontrol hout
  have hJ : ¬ elementaryAbelianMaxJ R₀ ≤ starKernel K R := by
    intro hh
    have hle : elementaryAbelianMaxJ R₀ ≤ pCore 2 J := hCR ▸
      le_inf (sSup_le fun _ hA => hA.1) hh
    have he := elementaryAbelianMaxJ_eq_of_intermediate R₀ (pCore 2 J) hle hQR
    have hm := congrArg (map J.subtype) he
    rw [← elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
      ← elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right)] at hm
    exact hth hm.ge
  have hA : ∃ A, A ∈ elementaryAbelianMaxSubgroups R₀ ∧ ¬ A ≤ starKernel K R := by
    by_contra! hh
    exact hJ (sSup_le hh)
  obtain ⟨A,hA,hne⟩ := hA
  have hb := maxElementary_isBestOffender V q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) R₀ A hVR hA
    (fun hbot => hne (by
      have hh := (Subgroup.map_eq_bot_iff A).mp hbot
      simpa only [show q.ker = starKernel K R from QuotientGroup.ker_mk' _] using hh))
  have hbest : IsStarBestOffender K R (A.map q) := hb
  exact ⟨hth,⟨A.map q,hbest.offender⟩,⟨A.map q,map_mono hA.1,hbest⟩⟩
end CFSG.Quasithin.ChapterC.C27Source

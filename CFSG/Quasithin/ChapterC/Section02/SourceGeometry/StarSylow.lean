module

public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.StarRadical
public import Theory.GroupTheory.SylowNormalSupplementRecognition

/-!
# Lifting a component Sylow from the actual star radical

If R* contains a Sylow subgroup of K*, its normal supplement makes R*
Sylow in K*R*. The original R is then Sylow in KR: its intersection with
the star kernel already contains the whole two-part O₂(KR). This applies
to the Sylow alternative of the classical radical theorem, including when
R* acts externally on K*.

Source: Aschbacher--Smith C.2.7(3), pp.146--147.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

theorem radical_sylow_of_star_component_sylow
    (h : Input κ H R M K) [(K.subgroupOf H).Normal]
    (S : Sylow 2 (starImage K R K))
    (hSR : (S : Subgroup _).map (starImage K R K).subtype ≤ starImage K R R) :
    ∃ P : Sylow 2 (K ⊔ R : Subgroup G),
      (P : Subgroup _) = R.subgroupOf (K ⊔ R) := by
  let D := K ⊔ R
  let R₀ := R.subgroupOf D
  let C := starImage K R K
  let q := QuotientGroup.mk' (starKernel K R)
  let : (K.subgroupOf D).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  let : C.Normal := (inferInstance : (K.subgroupOf D).Normal).map q
    (QuotientGroup.mk'_surjective _)
  have hR : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  obtain ⟨T,hT⟩ := exists_sylow_eq_of_normal_supplement C (starImage K R R)
    (hR.comap_subtype.map q) (starImage_sup_eq_top K R) S hSR
  obtain ⟨P,hRP⟩ := hR.comap_subtype.exists_le_sylow (P := R₀)
  have hTP : (T : Subgroup (StarQuotient K R)) ≤ (P : Subgroup D).map q := by
    rw [hT]
    exact map_mono hRP
  have hPm : (P : Subgroup D).map q = R₀.map q :=
    (T.is_maximal' (P.isPGroup'.map q) hTP).trans hT
  have hQR : pCore 2 D ≤ R₀ := fun x hx => source_joinCore_le_radical h
    (mem_map_of_mem D.subtype hx)
  have hPN := twoSubgroup_inf_starKernel_of_normal_input h (P : Subgroup D)
    P.isPGroup' (hQR.trans hRP)
  refine ⟨P,le_antisymm ?_ hRP⟩
  intro x hx
  have hximage : q x ∈ R₀.map q := hPm ▸ mem_map_of_mem q hx
  obtain ⟨r,hr,he⟩ := hximage
  have hxn : x*r⁻¹ ∈ starKernel K R := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (x*r⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hxQ : x*r⁻¹ ∈ pCore 2 D := hPN ▸
    (show x*r⁻¹ ∈ (P : Subgroup D) ⊓ starKernel K R from
      ⟨P.mul_mem hx (P.inv_mem (hRP hr)),hxn⟩)
  simpa only [inv_mul_cancel_right] using R₀.mul_mem (hQR hxQ) hr

end CFSG.Quasithin.ChapterC.C27Source

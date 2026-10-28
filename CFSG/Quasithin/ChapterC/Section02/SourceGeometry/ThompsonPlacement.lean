module

public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RadicalControl

/-!
# Radical-intersection placement from the actual Thompson image

It suffices that J(R)* lies in K*, even when R* has an outer action.
Intersect R with the inverse image of K*. This intermediate subgroup contains
J(R), so Thompson heredity identifies its Thompson subgroup with J(R).
The two-stage normalizer lift then puts the normalizer of R*∩K* inside the
normalizer of J(R)*, and the original C.2.3 control places it in M_K*.

Source: the normalizer placement in Aschbacher--Smith C.2.7(3), pp.146--147.
The component-containment premise is supplied by the actual B.5 row.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

theorem star_intersection_normalizer_control_of_thompson_inner
    (h : Input κ H R M K) [(K.subgroupOf H).Normal]
    (hinner : starImage K R (elementaryAbelianMaxJ R) ≤ starImage K R K) :
    normalizer ((starImage K R R).subgroupOf (starImage K R K) :
        Set (starImage K R K)) ≤
      (starM K R M).subgroupOf (starImage K R K) := by
  let D := K ⊔ R
  let R₀ := R.subgroupOf D
  let q := QuotientGroup.mk' (starKernel K R)
  let C := starImage K R K
  let A := R₀ ⊓ C.comap q
  have hJR : elementaryAbelianMaxJ R ≤ D :=
    (sSup_le fun _ hA => hA.1).trans (show R ≤ D from le_sup_right)
  have hJ : elementaryAbelianMaxJ R₀ = (elementaryAbelianMaxJ R).subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [←elementaryAbelianMaxJ_map_injective D.subtype D.subtype_injective,
      map_subgroupOf_eq_of_le (show R ≤ D from le_sup_right),
      map_subgroupOf_eq_of_le hJR]
  have hJA : elementaryAbelianMaxJ R₀ ≤ A := by
    refine le_inf (sSup_le fun _ hB => hB.1) ?_
    apply map_le_iff_le_comap.mp
    simpa only [hJ, starImage, q, C, D] using hinner
  have heJ : elementaryAbelianMaxJ A = elementaryAbelianMaxJ R₀ :=
    elementaryAbelianMaxJ_eq_of_intermediate R₀ A hJA inf_le_left
  have hR : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  have hQA : pCore 2 D ≤ A := by
    refine le_inf (fun x hx => source_joinCore_le_radical h
      (mem_map_of_mem D.subtype hx)) ?_
    intro x hx
    change q x ∈ C
    have hqx : q x = 1 := (QuotientGroup.eq_one_iff _).mpr (core_le_starKernel K R hx)
    rw [hqx]
    exact C.one_mem
  have hcop : Nat.Coprime 2 (Nat.card (q.ker.map (QuotientGroup.mk' (pCore 2 D)))) := by
    simpa only [q, QuotientGroup.ker_mk'] using
      starKernel_core_image_coprime_of_normal_input h
  have hn := QuasisimpleThompson.normalizer_image_le_normalizer_maxJ_of_odd_core_kernel
    A (hR.comap_subtype.to_le inf_le_left) q (QuotientGroup.mk'_surjective _)
    (pCore 2 D) hQA
    (by simpa only [q,QuotientGroup.ker_mk'] using core_le_starKernel K R) hcop
  have hAm : A.map q = starImage K R R ⊓ C := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨mem_map_of_mem q ha.1,ha.2⟩
    · rintro ⟨⟨a,ha,rfl⟩,hc⟩
      exact ⟨a,⟨ha,hc⟩,rfl⟩
  rw [heJ,hJ,hAm] at hn
  intro x hx
  have hxN : (x : StarQuotient K R) ∈
      normalizer ((starImage K R R ⊓ C : Subgroup (StarQuotient K R)) : Set (StarQuotient K R)) := by
    rw [←subgroupOf_map_subtype (starImage K R R) C]
    exact ((starImage K R R).subgroupOf C).le_normalizer_map C.subtype ⟨x,hx,rfl⟩
  exact (star_thompson_intersection_of_normal_input h).1 ⟨x.property,hn hxN⟩

theorem star_intersection_radical_of_thompson_inner
    (h : Input κ H R M K) [(K.subgroupOf H).Normal]
    (hinner : starImage K R (elementaryAbelianMaxJ R) ≤ starImage K R K) :
    IsPRadical 2 ((starImage K R R).subgroupOf (starImage K R K)) := by
  apply star_intersection_radical_of_normal_input h
  intro he
  have hjR : starImage K R (elementaryAbelianMaxJ R) ≤ starImage K R R :=
    map_mono (comap_mono (sSup_le fun _ hA => hA.1))
  have hz : starImage K R (elementaryAbelianMaxJ R) = ⊥ := by
    apply bot_unique
    have hle := le_inf hjR hinner
    have hm := congrArg (map (starImage K R K).subtype) he
    rw [subgroupOf_map_subtype,Subgroup.map_bot] at hm
    exact hle.trans hm.le
  have hJR : elementaryAbelianMaxJ R ≤ K ⊔ R :=
    (sSup_le fun _ hA => hA.1).trans (show R ≤ K ⊔ R from le_sup_right)
  have hJ : elementaryAbelianMaxJ (R.subgroupOf (K ⊔ R)) =
      (elementaryAbelianMaxJ R).subgroupOf (K ⊔ R) := by
    apply map_injective (K ⊔ R : Subgroup G).subtype_injective
    rw [←elementaryAbelianMaxJ_map_injective _ (K ⊔ R : Subgroup G).subtype_injective,
      map_subgroupOf_eq_of_le (show R ≤ K ⊔ R from le_sup_right),
      map_subgroupOf_eq_of_le hJR]
  apply thompson_not_le_starKernel_of_normal_input h
  rw [hJ]
  have hh := (map_eq_bot_iff ((elementaryAbelianMaxJ R).subgroupOf (K ⊔ R))).mp hz
  simpa only [QuotientGroup.ker_mk'] using hh

end CFSG.Quasithin.ChapterC.C27Source

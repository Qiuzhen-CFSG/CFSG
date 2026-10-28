module

public import Theory.GroupTheory.PRadical.NormalComponentImages
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.ThompsonControl
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.SourceCore

/-!
# The literal radical intersection in the star component

Intersect the original radical R with the relatively normal component K.
Normalizer saturation identifies its two-core. Pass first through O₂(K),
then through the odd central kernel of K/O₂(K) → K*. The resulting subgroup
is exactly R* ∩ K*: the full star kernel lies in O₂(KR)K and O₂(KR) ≤ R.
Consequently this actual intersection is two-radical whenever nontrivial.
The zero intersection remains a separate outer-action case.

Source: Aschbacher (1981), Lemma 8.2(4), in the C.2.7 geometry on pp.146–147.
This supplies the genuine radical input for classical flag-normalizer results.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

theorem component_intersection_normalizer_core_of_normal_input
    (h : Input κ H R M K) [(K.subgroupOf H).Normal] :
    (normalizer (R.subgroupOf K : Set K)).pCoreIn 2 = R.subgroupOf K := by
  let KH := K.subgroupOf H
  let RH := R.subgroupOf H
  let U := RH.subgroupOf KH
  let e : KH ≃* K := subgroupOfEquivOfLe h.component.1
  have hu : U.map e.toMonoidHom = R.subgroupOf K := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨⟨x,h.component.1 x.property⟩,x.property⟩,hx,rfl⟩
  have he := congrArg (map e.toMonoidHom)
    (normal_intersection_relative_core KH RH h.setup.radical)
  change ((normalizer (U : Set KH)).pCoreIn 2).map e.toMonoidHom = U.map e.toMonoidHom at he
  rwa [map_pCoreIn_of_injective 2 _ _ e.injective,map_equiv_normalizer_eq,hu] at he

theorem star_component_intersection_normalizer_core_of_normal_input
    (h : Input κ H R M K) [(K.subgroupOf H).Normal] :
    (normalizer ((R.subgroupOf K).map (toStarImage K R) : Set (starImage K R K))).pCoreIn 2 =
      (R.subgroupOf K).map (toStarImage K R) := by
  let U := R.subgroupOf K
  let q := QuotientGroup.mk' (pCore 2 K)
  let f := coreToStar h.normalizes
  have hR : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  have hU : IsPGroup 2 U := hR.comap_subtype
  have hc : (normalizer (U : Set K)).pCoreIn 2 = U :=
    component_intersection_normalizer_core_of_normal_input h
  have hQU : q.ker ≤ U := by
    rw [QuotientGroup.ker_mk']
    exact pCore_le_of_pCore_normalizer_le U hU hc.le
  have hquot := map_normalizer_core_of_p_kernel U hU hc q
    (QuotientGroup.mk'_surjective _) hQU
  have hk : f.ker ≤ center (K ⧸ pCore 2 K) :=
    coreToStar_ker_le_center_of_bound h.normalizes (kernel_offender_of_normal_input h).1.upper
  have hp : Nat.Coprime 2 (Nat.card f.ker) := Nat.prime_two.coprime_iff_not_dvd.mpr
    (PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) f.ker hk)
  have hs := map_normalizer_core_of_central_coprime_kernel (U.map q) (hU.map q) hquot f
    (coreToStar_surjective h.normalizes) hk hp
  have he : f.comp q = toStarImage K R := by ext k; rfl
  simpa only [map_map,he] using hs

theorem star_component_intersection_radical_of_normal_input
    (h : Input κ H R M K) [(K.subgroupOf H).Normal]
    (hne : (R.subgroupOf K).map (toStarImage K R) ≠ ⊥) :
    IsPRadical 2 ((R.subgroupOf K).map (toStarImage K R)) :=
  ⟨hne,star_component_intersection_normalizer_core_of_normal_input h⟩

theorem star_image_inf_component_of_normal_input
    (h : Input κ H R M K) [(K.subgroupOf H).Normal] :
    starImage K R (R ⊓ K) = starImage K R R ⊓ starImage K R K := by
  let J := K ⊔ R
  let R₀ := R.subgroupOf J
  let K₀ := K.subgroupOf J
  let q := QuotientGroup.mk' (starKernel K R)
  have hP : pCore 2 J ≤ q.ker := by
    rw [QuotientGroup.ker_mk']
    exact core_le_starKernel K R
  have hPR : pCore 2 J ≤ R₀ := fun x hx => source_joinCore_le_radical h
    (mem_map_of_mem J.subtype hx)
  have hC : coreCenterImage K R ≤ K₀ := by
    rintro x ⟨k,hk,rfl⟩
    exact k.property
  have hk : q.ker ≤ pCore 2 J ⊔ K₀ := by
    rw [QuotientGroup.ker_mk']
    exact (kernel_offender_of_normal_input h).1.upper.trans (sup_le_sup_left hC _)
  have hs := map_inf_of_kernel_le_sup R₀ K₀ (pCore 2 J) q hP hPR hk
  simpa only [starImage,subgroupOf,comap_inf,R₀,K₀,q,J] using hs

omit [Finite G] in
theorem component_intersection_star_map (K R : Subgroup G) :
    ((R.subgroupOf K).map (toStarImage K R)).map (starImage K R K).subtype =
      starImage K R (R ⊓ K) := by
  ext x
  constructor
  · rintro ⟨y,⟨k,hk,rfl⟩,rfl⟩
    exact ⟨inclusion (show K ≤ K ⊔ R from le_sup_left) k,⟨hk,k.property⟩,rfl⟩
  · rintro ⟨k,hk,rfl⟩
    exact ⟨toStarImage K R ⟨k,hk.2⟩,⟨⟨k,hk.2⟩,hk.1,rfl⟩,rfl⟩

theorem component_intersection_star_eq_of_normal_input
    (h : Input κ H R M K) [(K.subgroupOf H).Normal] :
    (R.subgroupOf K).map (toStarImage K R) =
      (starImage K R R).subgroupOf (starImage K R K) := by
  apply map_injective (starImage K R K).subtype_injective
  rw [component_intersection_star_map,star_image_inf_component_of_normal_input h,
    subgroupOf_map_subtype]

theorem star_intersection_normalizer_core_of_normal_input
    (h : Input κ H R M K) [(K.subgroupOf H).Normal] :
    (normalizer ((starImage K R R).subgroupOf (starImage K R K) : Set (starImage K R K))).pCoreIn 2 =
      (starImage K R R).subgroupOf (starImage K R K) := by
  rw [←component_intersection_star_eq_of_normal_input h]
  exact star_component_intersection_normalizer_core_of_normal_input h

theorem star_intersection_radical_of_normal_input
    (h : Input κ H R M K) [(K.subgroupOf H).Normal]
    (hne : (starImage K R R).subgroupOf (starImage K R K) ≠ ⊥) :
    IsPRadical 2 ((starImage K R R).subgroupOf (starImage K R K)) :=
  ⟨hne,star_intersection_normalizer_core_of_normal_input h⟩
end CFSG.Quasithin.ChapterC.C27Source


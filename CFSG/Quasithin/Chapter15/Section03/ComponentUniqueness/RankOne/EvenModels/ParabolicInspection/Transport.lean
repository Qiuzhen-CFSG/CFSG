module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BorelContracts
public import Theory.GroupTheory.SylowImageIntersection
public import Theory.GroupTheory.Fitting.Centralizer


/-!
# Lifting the Borel inspection through the component action quotient

The kernel `C_I(L)` lies in `M_I` by the given normalizer identity. On
restricting the action map to `L`, its kernel is `Z(L) = O₂(L)`, contained
in the supplied component Sylow subgroup. Sylow maximality identifies the
intersection of the quotient images with the image of that Sylow subgroup.
Consequently the preimage of the quotient Sylow normalizer is exactly the
upstairs Sylow normalizer. This lifts a quotient Borel equality without
removing the permitted nontrivial central two-covers.

The original three-prime residual lies in `L`. Its prime-power generators
therefore give the same residual inside `M ∩ L`, both upstairs and in the
action quotient. Properness and Sylow invariance of the quotient local
intersection are also consequences of the actual reduction data.

These transport results do not classify a parabolic or prove a surviving
model alternative; `largerFieldBorel_of_quotient` leaves both inspection
outputs explicit.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43, printed p.1140, the characteristic-two paragraphs.
-/

public section

open Subgroup
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)

omit [Finite G] in
theorem componentMap_preimage_local :
    ((c.toComponentAction.image M).subgroupOf (c.toComponentAction.image L)).comap
      c.toComponentAction.componentMap = M.subgroupOf L := by
  have hk : c.toComponentAction.quotientMap.ker ≤ M.subgroupOf I := by
    rw [show c.toComponentAction.quotientMap.ker = c.toComponentAction.kernel from
      QuotientGroup.ker_mk' _]
    exact c.toComponentAction.kernel_le_intersection c.y_le_component c.normalizer_eq
  ext x
  change c.toComponentAction.quotientMap ⟨x, c.component_le x.property⟩ ∈
    (M.subgroupOf I).map c.toComponentAction.quotientMap ↔ (x : G) ∈ M
  change (⟨x, c.component_le x.property⟩ : I) ∈
    ((M.subgroupOf I).map c.toComponentAction.quotientMap).comap
      c.toComponentAction.quotientMap ↔ _
  rw [comap_map_eq_self hk]
  rfl

theorem componentMap_sylow_image :
    ((S.subgroupOf L).map c.toComponentAction.componentMap).map
      (c.toComponentAction.image L).subtype =
        c.toComponentAction.image S ⊓ c.toComponentAction.image L := by
  obtain ⟨P, hP⟩ := c.sylow
  have hSP : S.subgroupOf I = (P : Subgroup I) := by
    rw [← hP, subgroupOf, comap_map_eq_self_of_injective I.subtype_injective]
  let : (L.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer c.normalizes
  obtain ⟨R, hR⟩ := P.exists_subgroupOf_eq_of_normal (L.subgroupOf I)
  have he := P.map_image_eq_inf (L.subgroupOf I)
    ((P : Subgroup I) ⊓ L.subgroupOf I) R
    (by rw [hR, subgroupOf_map_subtype]) inf_le_left c.toComponentAction.quotientMap
  rw [← hSP] at he
  change _ = (S.subgroupOf I).map c.toComponentAction.quotientMap ⊓
    (L.subgroupOf I).map c.toComponentAction.quotientMap
  rw [← he]
  ext x
  constructor
  · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨⟨s, c.component_le s.property⟩, ⟨hs, s.property⟩, rfl⟩
  · rintro ⟨s, ⟨hs, hl⟩, rfl⟩
    exact ⟨c.toComponentAction.componentMap ⟨s, hl⟩, ⟨⟨s, hl⟩, hs, rfl⟩, rfl⟩

theorem componentMap_preimage_sylow :
    ((c.toComponentAction.image S).subgroupOf (c.toComponentAction.image L)).comap
      c.toComponentAction.componentMap = S.subgroupOf L := by
  have he : (c.toComponentAction.image S).subgroupOf (c.toComponentAction.image L) =
      (S.subgroupOf L).map c.toComponentAction.componentMap := by
    apply Subgroup.map_injective (c.toComponentAction.image L).subtype_injective
    rw [subgroupOf_map_subtype, componentMap_sylow_image c]
  rw [he, comap_map_eq_self]
  rw [c.toComponentAction.componentMap_ker, center_eq_twoCore c]
  obtain ⟨P, hP⟩ := component_sylow c
  have hp := fitting_pCore_le_sylow P
  have hSP : S.subgroupOf L = (P : Subgroup L) := by
    apply Subgroup.map_injective L.subtype_injective
    rw [subgroupOf_map_subtype, hP]
  rwa [hSP]

omit [Finite G] c in
private theorem borel_subgroupOf (L S : Subgroup G) :
    (borel L S).subgroupOf L = normalizer (S.subgroupOf L : Set L) := by
  rw [borel, inf_subgroupOf_left, subgroupOf_normalizer_eq inf_le_right,
    inf_subgroupOf_right]

theorem componentMap_preimage_borel :
    ((borel (c.toComponentAction.image L) (c.toComponentAction.image S)).subgroupOf
      (c.toComponentAction.image L)).comap c.toComponentAction.componentMap =
        (borel L S).subgroupOf L := by
  rw [borel_subgroupOf, borel_subgroupOf,
    comap_normalizer_eq_of_surjective _ c.toComponentAction.componentMap_surjective,
    componentMap_preimage_sylow c]

/-- The quotient Borel identity recovers the literal upstairs normalizer,
including when the component has a nontrivial central two-cover. -/
theorem intersection_eq_borel_of_quotient
    (hB : c.toComponentAction.image M ⊓ c.toComponentAction.image L =
      borel (c.toComponentAction.image L) (c.toComponentAction.image S)) :
    M ⊓ L = borel L S := by
  have he := congrArg (fun H : Subgroup c.toComponentAction.Quotient =>
    (H.subgroupOf (c.toComponentAction.image L)).comap c.toComponentAction.componentMap) hB
  rw [inf_subgroupOf_right, componentMap_preimage_local c, componentMap_preimage_borel c] at he
  have hm := congrArg (fun H : Subgroup L => H.map L.subtype) he
  rw [subgroupOf_map_subtype, map_subgroupOf_eq_of_le
    (show borel L S ≤ L from inf_le_left)] at hm
  exact hm

theorem largerFieldBorel_of_quotient {n : ℕ} (hm : BorelModel L n)
    (hB : c.toComponentAction.image M ⊓ c.toComponentAction.image L =
      borel (c.toComponentAction.image L) (c.toComponentAction.image S)) :
    LargerFieldBorel S M L n :=
  ⟨hm, intersection_eq_borel_of_quotient c hB⟩

omit [Finite G] in
theorem quotient_intersection_proper :
    c.toComponentAction.image M ⊓ c.toComponentAction.image L <
      c.toComponentAction.image L := by
  refine lt_of_le_of_ne inf_le_right ?_
  intro he
  have hLM : c.toComponentAction.image L ≤ c.toComponentAction.image M :=
    he ▸ inf_le_left
  have htop : (c.toComponentAction.image M).subgroupOf (c.toComponentAction.image L) = ⊤ :=
    subgroupOf_eq_top.mpr hLM
  have hpre := componentMap_preimage_local c
  rw [htop, comap_top] at hpre
  exact c.component_outside (subgroupOf_eq_top.mp hpre.symm)

omit [Finite G] in
theorem quotient_sylow_normalizes_intersection :
    c.toComponentAction.image S ≤ normalizer
      (c.toComponentAction.image M ⊓ c.toComponentAction.image L : Set c.toComponentAction.Quotient) := by
  have hSM : c.toComponentAction.image S ≤ c.toComponentAction.image M :=
    map_mono (fun _ hx => c.sylow_le_M hx)
  apply (le_inf (hSM.trans (c.toComponentAction.image M).le_normalizer)
    (show c.toComponentAction.image S ≤ normalizer
      (c.toComponentAction.image L : Set c.toComponentAction.Quotient) from ?_)).trans
    inf_normalizer_le_normalizer_inf
  rw [normalizer_eq_top]
  exact le_top

omit [Finite G] c in
private theorem threeResidual_intersection {Y X K : Subgroup G}
    (hY : Y = threeResidualIn X) (hYK : Y ≤ K) :
    Y = threeResidualIn (X ⊓ K) := by
  have hsmall : threeResidualIn X ≤ K := hY ▸ hYK
  rw [hY, threeResidualIn, threeResidualIn, map_primePowerGenerated_subtype,
    map_primePowerGenerated_subtype]
  apply le_antisymm
  · rw [closure_le]
    intro x hx
    apply Subgroup.subset_closure
    exact ⟨⟨hx.1, hsmall (by
      rw [threeResidualIn, map_primePowerGenerated_subtype]
      exact subset_closure hx)⟩, hx.2⟩
  · exact closure_mono (fun _ hx => ⟨hx.1.1, hx.2⟩)

omit [Finite G] in
include c in
theorem residual_on_component : Yplus = threeResidualIn (M ⊓ L) := by
  have he := threeResidual_intersection c.residual c.y_le_component
  have hi : (M ⊓ I) ⊓ L = M ⊓ L := by
    rw [inf_assoc, inf_eq_right.mpr c.component_le]
  rwa [hi] at he

omit [Finite G] in
theorem quotient_residual_on_component :
    c.toComponentAction.image Yplus = threeResidualIn
      (c.toComponentAction.image M ⊓ c.toComponentAction.image L) :=
  threeResidual_intersection c.quotient.residual
    (map_mono (fun _ hx => c.y_le_component hx))

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.ThompsonPlacement

/-!
# The actual radical inside the offender group

The original Thompson image is nontrivial and lies in both the radical image
and the offender group. If the component fills the offender group, this also
puts the Thompson image in the component, so its radical intersection is a
genuine nontrivial radical. These statements retain the original star kernel.
Source: Aschbacher--Smith C.2.7, pp.146--147.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

/-- The actual Thompson image survives the original star kernel. -/
theorem star_thompson_ne_bot_from_source (h : Input κ H R M K) :
    starImage K R (elementaryAbelianMaxJ R) ≠ ⊥ := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  intro hz
  have hJR : elementaryAbelianMaxJ R ≤ K ⊔ R :=
    (sSup_le fun _ hA => hA.1).trans (show R ≤ K ⊔ R from le_sup_right)
  have hJ : elementaryAbelianMaxJ (R.subgroupOf (K ⊔ R)) =
      (elementaryAbelianMaxJ R).subgroupOf (K ⊔ R) := by
    apply map_injective (K ⊔ R : Subgroup G).subtype_injective
    rw [←elementaryAbelianMaxJ_map_injective _ (K ⊔ R : Subgroup G).subtype_injective,
      map_subgroupOf_eq_of_le (show R ≤ K ⊔ R from le_sup_right),
      map_subgroupOf_eq_of_le hJR]
  apply thompson_not_le_starKernel_of_normal_input (source_join_input h)
  rw [hJ]
  have hh := (map_eq_bot_iff ((elementaryAbelianMaxJ R).subgroupOf (K ⊔ R))).mp hz
  simpa only [QuotientGroup.ker_mk'] using hh

/-- The literal radical intersection with the offender group is nontrivial. -/
theorem star_radical_offender_ne_bot_from_source (h : Input κ H R M K) :
    (starImage K R R).subgroupOf (offenderSubgroup (starRepresentation K R)) ≠ ⊥ := by
  intro he
  have hjR : starImage K R (elementaryAbelianMaxJ R) ≤ starImage K R R :=
    map_mono (comap_mono (sSup_le fun _ hA => hA.1))
  have hm := congrArg (map (offenderSubgroup (starRepresentation K R)).subtype) he
  rw [subgroupOf_map_subtype,Subgroup.map_bot] at hm
  apply star_thompson_ne_bot_from_source h
  exact bot_unique ((le_inf hjR (star_thompson_le_offenderSubgroup_from_source h)).trans hm.le)

/-- The actual whole-actor row supplies the nontrivial component radical. -/
theorem star_intersection_radical_of_whole_offender_from_source
    (h : Input κ H R M K)
    (hwhole : (starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R)) = ⊤) :
    IsPRadical 2 ((starImage K R R).subgroupOf (starImage K R K)) := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  apply star_intersection_radical_of_thompson_inner (source_join_input h)
  exact (star_thompson_le_offenderSubgroup_from_source h).trans
    (subgroupOf_eq_top.mp hwhole)

end CFSG.Quasithin.ChapterC.C27Source

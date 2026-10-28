module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Contracts
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Transport
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Nilpotent

/-!
# Residual constraints in the component action quotient

The kernel of the actor map embeds in `Z(L) = O₂(L)`. Lifting the two-core
through this two-group kernel preserves the index three exactly. Thus the
actual parabolic has three-rank at most one and solvable `O^{3′}` residual.
The specified Sylow intersection is transported through the same quotient.
These facts retain the nontrivial central two-covers.

The final two transport lemmas pass Borel containment upstairs and Borel
equality downstairs. None of these facts identifies a surviving model or
assumes solvability of the entire parabolic.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43(a), (e) and the characteristic-two paragraphs, printed pp.1139--1140.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)

/-- The quotient map restricted to the original residual actor. -/
def actorMap : Yplus →* c.toComponentAction.image Yplus :=
  (c.toComponentAction.quotientMap.subgroupMap (Yplus.subgroupOf I)).comp
    (subgroupOfEquivOfLe (c.y_le_component.trans c.component_le)).symm.toMonoidHom

omit [Finite G] in
theorem actorMap_surjective : Function.Surjective (actorMap c) :=
  (c.toComponentAction.quotientMap.subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe (c.y_le_component.trans c.component_le)).symm.surjective

omit [Finite G] in
theorem actorMap_kernel_isTwoGroup : IsPGroup 2 (actorMap c).ker := by
  have hz : IsPGroup 2 (center L) := by
    rw [center_eq_twoCore c]
    exact pCore_isPGroup
  let f : (actorMap c).ker →* center L := {
    toFun := fun x => ⟨⟨x.val, c.y_le_component x.val.property⟩, by
      have he : c.toComponentAction.quotientMap
          ⟨x.val, c.y_le_component.trans c.component_le x.val.property⟩ = 1 :=
        congrArg Subtype.val x.property
      have hc := (QuotientGroup.eq_one_iff _).mp he
      exact mem_center_iff.mpr (fun l => Subtype.ext (hc l l.property))⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  exact hz.of_injective f (fun x y he => Subtype.ext (Subtype.ext
    (congrArg (fun z : center L => ((z : L) : G)) he)))

theorem quotient_actor_index : (pCore 2 (c.toComponentAction.image Yplus)).index = 3 := by
  have he := (actorMap c).comap_pCore_of_ker_isPGroup
    (actorMap_surjective c) (actorMap_kernel_isTwoGroup c)
  rw [← c.index, ← he]
  exact ((pCore 2 (c.toComponentAction.image Yplus)).index_comap_of_surjective
    (actorMap_surjective c)).symm

include c in
theorem actor_solvable : Group.IsSolvable Yplus := by
  let : Group.IsNilpotent (pCore 2 Yplus) :=
    (pCore_isPGroup (p := 2) (G := Yplus)).isNilpotent
  let : IsCyclic (Yplus ⧸ pCore 2 Yplus) :=
    isCyclic_of_prime_card (show Nat.card (Yplus ⧸ pCore 2 Yplus) = 3 from c.index)
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 Yplus)).mpr
    ⟨inferInstance, inferInstance⟩

theorem quotient_actor_solvable : Group.IsSolvable (c.toComponentAction.image Yplus) := by
  let : Group.IsSolvable Yplus := actor_solvable c
  exact Group.isSolvable_of_surjective (actorMap_surjective c)

omit [Finite G] in
private theorem intersection_subgroupOf_eq (hB : M ⊓ L = borel L S) :
    M.subgroupOf L = (borel L S).subgroupOf L := by
  rw [← hB, inf_subgroupOf_right]

theorem quotient_intersection_eq_borel_of_intersection
    (hB : M ⊓ L = borel L S) :
    c.toComponentAction.image M ⊓ c.toComponentAction.image L =
      borel (c.toComponentAction.image L) (c.toComponentAction.image S) := by
  have he : (c.toComponentAction.image M).subgroupOf (c.toComponentAction.image L) =
      (borel (c.toComponentAction.image L) (c.toComponentAction.image S)).subgroupOf
        (c.toComponentAction.image L) := by
    apply Subgroup.comap_injective c.toComponentAction.componentMap_surjective
    rw [componentMap_preimage_local c, componentMap_preimage_borel c]
    exact intersection_subgroupOf_eq hB
  have hm := congrArg (fun H : Subgroup (c.toComponentAction.image L) =>
    H.map (c.toComponentAction.image L).subtype) he
  rwa [subgroupOf_map_subtype, map_subgroupOf_eq_of_le
    (show borel _ _ ≤ c.toComponentAction.image L from inf_le_left)] at hm

theorem borel_le_intersection (hp : QuotientParabolic c) : borel L S ≤ M ⊓ L := by
  have hle := Subgroup.comap_mono (f := c.toComponentAction.componentMap)
    (Subgroup.subgroupOf_mono (c.toComponentAction.image L) hp.contains_borel)
  rw [inf_subgroupOf_right, componentMap_preimage_local c,
    componentMap_preimage_borel c] at hle
  have hm := Subgroup.map_mono (f := L.subtype) hle
  rwa [map_subgroupOf_eq_of_le (show borel L S ≤ L from inf_le_left),
    subgroupOf_map_subtype] at hm

/-- The full Sylow intersection survives in the component action quotient. -/
theorem quotient_component_sylow :
    ∃ P : Sylow 2 (c.toComponentAction.image L),
      (P : Subgroup (c.toComponentAction.image L)).map
        (c.toComponentAction.image L).subtype =
          c.toComponentAction.image S ⊓ c.toComponentAction.image L := by
  obtain ⟨P, hP⟩ := component_sylow c
  have hSP : S.subgroupOf L = (P : Subgroup L) := by
    apply Subgroup.map_injective L.subtype_injective
    rw [subgroupOf_map_subtype, hP]
  refine ⟨P.mapSurjective c.toComponentAction.componentMap_surjective, ?_⟩
  change ((P : Subgroup L).map c.toComponentAction.componentMap).map _ = _
  rw [← hSP]
  exact componentMap_sylow_image c

/-- The cubic index controls the actual parabolic, not just the residual's rank. -/
theorem quotient_parabolic_threeRank :
    primeRank 3 (c.toComponentAction.image M ⊓ c.toComponentAction.image L :
      Subgroup c.toComponentAction.Quotient) ≤ 1 :=
  threeRank_le_one_of_residual_index (quotient_residual_on_component c)
    (quotient_actor_index c)

/-- This is the solvability obstruction to a nontrivial Levi three-residual. -/
theorem quotient_parabolic_residual_solvable :
    Group.IsSolvable (threeResidualIn
      (c.toComponentAction.image M ⊓ c.toComponentAction.image L)) := by
  rw [← quotient_residual_on_component c]
  exact quotient_actor_solvable c

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

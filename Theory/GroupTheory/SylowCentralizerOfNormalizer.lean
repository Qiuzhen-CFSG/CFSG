module
public import Theory.GroupTheory.SylowNormalRestriction
public import Mathlib.GroupTheory.Subgroup.Centralizer
/-!
# A Sylow subgroup in a normalized subgroup's centralizer

If a supplied Sylow subgroup normalizes E, restrict it to N(E), then to the
normal subgroup C(E). Mapping the restriction back retains the exact
intersection S ∩ C(E). The original 13.9.1 application centralizes its marked
four-group inside the previously constructed Sylow of C_G(t).
-/
public section
open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_centralizer_sylow_of_normalizes
    (S : Sylow p G) (E : Subgroup G)
    (hS : (S : Subgroup G) ≤ normalizer (E : Set G)) :
    ∃ Q : Sylow p (centralizer (E : Set G)),
      (Q : Subgroup (centralizer (E : Set G))).map
        (centralizer (E : Set G)).subtype = (S : Subgroup G) ⊓ centralizer (E : Set G) := by
  let N := normalizer (E : Set G)
  let C := centralizer (E : Set G)
  let P := S.subtype hS
  obtain ⟨Q,hQ⟩ := P.exists_sylow_map_eq_inf_of_normal (C.subgroupOf N)
  let e : C.subgroupOf N ≃* C := subgroupOfEquivOfLe (centralizer_le_normalizer (E : Set G))
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((Q : Subgroup (C.subgroupOf N)).map e.toMonoidHom).map C.subtype = _
  calc
    _ = ((Q : Subgroup (C.subgroupOf N)).map (C.subgroupOf N).subtype).map N.subtype := by
      rw [map_map,map_map]
      rfl
    _ = ((P : Subgroup N) ⊓ C.subgroupOf N).map N.subtype := by rw [hQ]
    _ = (S : Subgroup G) ⊓ C := by
      rw [Subgroup.map_inf _ _ N.subtype N.subtype_injective]
      change ((S : Subgroup G).subgroupOf N).map N.subtype ⊓ (C.subgroupOf N).map N.subtype = _
      rw [map_subgroupOf_eq_of_le hS,map_subgroupOf_eq_of_le (centralizer_le_normalizer (E : Set G))]
end Sylow

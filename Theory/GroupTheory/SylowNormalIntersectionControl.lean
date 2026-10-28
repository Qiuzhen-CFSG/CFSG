module
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SylowCommutatorCore
/-!
# Sylow control inside a normal subgroup

A Sylow subgroup intersects a normal subgroup in a Sylow subgroup.
Consequently a p-subgroup of the intersection which normalizes that literal
Sylow image lies in it. The ambient embedding and intersection are retained;
normality is required only for the second subgroup.

Source application: Aschbacher–Smith C.2.4(2), via Aschbacher, Math. Z. 177
(1981), 10.3: apply this to the normal closure of the original radical in M
and the normalizer of the moved component.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem le_sylow_inf_normal_of_normalizes
    (H D : Subgroup G) [D.Normal] (S : Sylow p H) (Q K : Subgroup G)
    (hS : (S : Subgroup H).map H.subtype = Q)
    (hKp : IsPGroup p K) (hKH : K ≤ H) (hKD : K ≤ D)
    (hKn : K ≤ normalizer ((Q ⊓ D : Subgroup G) : Set G)) : K ≤ Q ⊓ D := by
  let D₀ := D.subgroupOf H
  obtain ⟨T,hT⟩ := S.exists_subgroupOf_eq_of_normal D₀
  have hmap : (T : Subgroup D₀).map D₀.subtype = (Q ⊓ D).subgroupOf H := by
    rw [hT, subgroupOf_map_subtype]
    ext x
    change (x ∈ S ∧ (x : G) ∈ D) ↔ ((x : G) ∈ Q ∧ (x : G) ∈ D)
    have hsx : (x : G) ∈ Q ↔ x ∈ S := by
      rw [← hS]
      exact mem_map_iff_mem H.subtype_injective
    rw [hsx]
  have hsub : K.subgroupOf H ≤ (Q ⊓ D).subgroupOf H := by
    apply le_sylow_image_of_normalizes D₀ T hmap hKp.comap_subtype
      (subgroupOf_mono H hKD)
    have hQD : Q ⊓ D ≤ H := inf_le_left.trans (hS ▸ map_subtype_le _)
    rw [← subgroupOf_normalizer_eq hQD]
    exact subgroupOf_mono H hKn
  intro x hx
  exact hsub (show (⟨x,hKH hx⟩ : H) ∈ K.subgroupOf H from hx)
end Subgroup

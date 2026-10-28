module

public import Theory.GroupTheory.SylowNormalizedSupIndex

/-!
# Sylow intersections after adjoining normalizing p-subgroups

Suppose the ambient Sylow p-subgroup intersects H in a Sylow subgroup of H.
Adjoining any subgroup U of that ambient Sylow which normalizes H preserves
this intersection property. Apply the coprime-index supplement criterion to
the intersection of the ambient Sylow with HU; its join with H is still HU.
All normality is relative to HU.

Source: the standard Sylow product argument, used for E.1.2(E0) in
Aschbacher--Smith, printed p.210. The PSL₃ tau-extension consumer is
`InnerFamilies.TauMembers`.
-/

public section
open Subgroup

namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Adjoining a normalizing subgroup of the ambient Sylow preserves Sylow intersection. -/
theorem exists_subgroupOf_sup_of_normalized (T : Sylow p G) (H U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUH : U ≤ normalizer H)
    (hHT : ∃ S : Sylow p H, (S : Subgroup H) = (T : Subgroup G).subgroupOf H) :
    ∃ S : Sylow p (H ⊔ U : Subgroup G),
      (S : Subgroup (H ⊔ U : Subgroup G)) = (T : Subgroup G).subgroupOf (H ⊔ U) := by
  let J := H ⊔ U
  let P := (T : Subgroup G) ⊓ J
  have hgen : H ⊔ P = J := le_antisymm (sup_le le_sup_left inf_le_right)
    (sup_le le_sup_left ((le_inf hUT le_sup_right).trans le_sup_right))
  have hPn : P ≤ normalizer H := inf_le_right.trans (sup_le H.le_normalizer hUH)
  obtain ⟨D, hD⟩ := hHT
  have hDP : (D : Subgroup H).map H.subtype ≤ P := by
    rw [hD, subgroupOf_map_subtype]
    exact inf_le_inf_left _ le_sup_left
  obtain ⟨S, hS⟩ := T.isPGroup'.to_le (inf_le_left : P ≤ (T : Subgroup G))
    |>.exists_sylow_sup_of_coprime_index H P hPn (D : Subgroup H) D.not_dvd_index hDP
  have hex : ∃ S : Sylow p (H ⊔ P : Subgroup G),
      (S : Subgroup (H ⊔ P : Subgroup G)).map (H ⊔ P).subtype = P := ⟨S,hS⟩
  rw [hgen] at hex
  obtain ⟨S, hS⟩ := hex
  refine ⟨S, map_injective J.subtype_injective ?_⟩
  rw [hS, subgroupOf_map_subtype]

end Sylow

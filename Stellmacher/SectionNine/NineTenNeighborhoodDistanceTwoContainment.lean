module
public import Stellmacher.SectionNine.NineTenDistanceTwoNeighborhood

/-!
# A neighboring module join lies in the literal distance-two join

If the module at a vertex lies in its exact-distance-two module join, then
so does the one-step module join at every neighbor. A two-step walk either
returns to the original vertex or has distinct endpoints. Bipartiteness
excludes adjacency in the latter case, so their distance is exactly two.

This supplies W_lambda≤W_first in the final branches of Stellmacher (9.10),
printed p.59. The self-module inclusion is supplied explicitly, and no
identification with the two-step-walk enlargement is required.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem distance_two_of_common_neighbor
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (first middle last : Γ.Vertex)
    (hfirst : Γ.adjacent first middle) (hlast : Γ.adjacent middle last)
    (hne : first ≠ last) : Γ.distance first last = 2 := by
  have hbound := Γ.distance_le_of_path 2 ![first,middle,last] (by
    intro i
    fin_cases i
    · exact hfirst
    · exact hlast)
  change Γ.distance first last ≤ 2 at hbound
  have hzero : Γ.distance first last ≠ 0 := fun h =>
    hne ((Γ.distance_zero_iff first last).mp h)
  have hnotadj : ¬ Γ.adjacent first last := by
    intro hfl
    rcases Γ.coset₁_surjective first with ⟨a,rfl|rfl⟩ <;>
      rcases Γ.coset₁_surjective middle with ⟨b,rfl|rfl⟩ <;>
      rcases Γ.coset₁_surjective last with ⟨c,rfl|rfl⟩ <;>
      first
      | exact Γ.no_adj_coset₁_coset₁ _ _ hfirst
      | exact Γ.no_adj_coset₂_coset₂ _ _ hfirst
      | exact Γ.no_adj_coset₁_coset₁ _ _ hlast
      | exact Γ.no_adj_coset₂_coset₂ _ _ hlast
      | exact Γ.no_adj_coset₁_coset₁ _ _ hfl
      | exact Γ.no_adj_coset₂_coset₂ _ _ hfl
  have hone : Γ.distance first last ≠ 1 := fun h =>
    hnotadj ((adjacent_iff_distance_eq_one Γ).mpr h)
  omega

public theorem nine_ten_neighborhood_le_distance_two_of_self_le
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (first middle : Γ.Vertex)
    (hmiddle : middle ∈ Neighborhood Γ first)
    (hself : VAt Γ first ≤ DistanceTwoNeighborhoodV Γ first) :
    GeneratedNeighborhoodV Γ middle ≤ DistanceTwoNeighborhoodV Γ first := by
  apply sSup_le
  rintro subgroup ⟨last,hlast,rfl⟩
  by_cases heq : first=last
  · rwa [←heq]
  exact v_le_distance_two_neighborhood Γ
    (distance_two_of_common_neighbor Γ first middle last
      ((mem_neighborhood_iff_adjacent Γ).mp hmiddle)
      ((mem_neighborhood_iff_adjacent Γ).mp hlast) heq)

end Stellmacher.SectionNine

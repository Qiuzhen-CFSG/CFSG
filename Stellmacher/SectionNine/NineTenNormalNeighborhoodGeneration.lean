module
public import Stellmacher.SectionNine.NineTenDistanceTwoNeighborhood

/-!
# Normalized containment of one neighborhood generates the distance-two join

For a Section Seven graph, a subgroup normalized by a vertex stabilizer and
containing the one-step module join at one of its neighbors contains the
literal distance-two module join at that vertex. No critical-length or order
hypothesis is needed.

The vertex stabilizer acts transitively on its neighbors. Conjugating the
supplied neighborhood join thus places every such join in the normalized
subgroup. Each distance-two module lies in one of these joins, using the
proved inclusion into the two-step-walk enlargement without asserting an
equality of the two definitions. This is the normal-join generation step
used in both final branches of Stellmacher (9.10), printed p.59.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_distance_two_le_of_normalized_neighborhood
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h7 : SectionSevenHypotheses G T A B) (Γ : CosetGraphContext G T A B)
    (vertex neighbor : Γ.Vertex) (hneighbor : neighbor ∈ Neighborhood Γ vertex)
    (K : Subgroup G) (hnormal : GAt Γ vertex ≤ Subgroup.normalizer (K : Set G))
    (hjoin : GeneratedNeighborhoodV Γ neighbor ≤ K) :
    DistanceTwoNeighborhoodV Γ vertex ≤ K := by
  apply (distance_two_neighborhood_le_source_odd_w Γ vertex).trans
  rw [SourceOddW]
  apply sSup_le
  rintro subgroup ⟨middle,hmiddle,endpoint,hendpoint,rfl⟩
  obtain ⟨actor,hactor⟩ := (lemma_seven_one h7 Γ).local_transitivity vertex hneighbor hmiddle
  have hmap : K.map (MulAut.conj (actor:G)⁻¹).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (hnormal ((GAt Γ vertex).inv_mem actor.property))
  have hmiddleJoin : GeneratedNeighborhoodV Γ middle ≤ K := by
    rw [←hactor,nine_seven_neighborhood_act]
    exact (Subgroup.map_mono hjoin).trans_eq hmap
  exact (nine_eight_v_le_generated_neighborhood Γ hendpoint).trans hmiddleJoin

end Stellmacher.SectionNine

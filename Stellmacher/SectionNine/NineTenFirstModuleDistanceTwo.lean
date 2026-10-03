module
public import Stellmacher.SectionNine.NineTenDistanceTwoNeighborhood
public import Stellmacher.SectionNine.NineSevenGoldschmidtPaths
public import Stellmacher.SectionNine.LemmaNineThree

/-!
# The first module lies in its own distance-two neighborhood join

For a commuting critical path of length greater than four, V at the first
step lies in the literal join of V-groups at distance two from that step.
This supplies the inclusion needed for the normal-subgroup construction
in the final distance-five case of (9.10).

Each center generator of the first module belongs to an adjacent vertex
in the initial orbit. The proved SL2(2) local quotient makes that vertex
cubic, so it has another neighbor. Bipartiteness and distinctness put that
neighbor at distance two from the first step, and its module contains the
original center. Joining these containments proves the assertion.

Source: Stellmacher, Journal of Algebra 190 (1997), the orbit-dependent
neighborhood definition on p.50 and (9.10), printed pp.58–59. The actual
ambient context and its graph are retained throughout.
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

public theorem nine_ten_first_module_le_distance_two_neighborhood
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 4 < ctx.criticalPath.length) :
    VAt ctx.Γ ctx.criticalPath.firstStep ≤
      DistanceTwoNeighborhoodV ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  change Γ.vAt cp.firstStep ≤ _
  rw [Γ.vAt_def]
  apply sSup_le
  rintro subgroup ⟨middle,hmiddle,rfl⟩
  have hadj : Γ.adjacent cp.firstStep middle :=
    (mem_neighborhood_iff_adjacent Γ).mp hmiddle
  have hinitial : cp.a ∈ neighborhood Γ cp.firstStep :=
    (mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
  obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
    cp.firstStep hinitial hmiddle
  have horbit : IsConjugateVertex Γ cp.a middle := ⟨mover,hmove⟩
  have hmodel := (lemma_nine_three_ambient ctx (by omega) middle horbit).1
  obtain ⟨last,hlast,hne⟩ := goldschmidt_neighbor_other Γ middle cp.firstStep
    (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven middle hmodel).degree
  have hdist : Γ.distance cp.firstStep last = 2 :=
    distance_two_of_common_neighbor Γ cp.firstStep middle last hadj hlast hne.symm
  have hcenter : ZAt Γ middle ≤ VAt Γ last :=
    nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hlast)
  exact hcenter.trans (v_le_distance_two_neighborhood Γ hdist)

end Stellmacher.SectionNine

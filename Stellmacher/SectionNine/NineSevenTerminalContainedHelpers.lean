module

public import Stellmacher.SectionNine.NineSevenNormalityObstructions

/-!
# Center and join identities for the contained branch of (9.7)

Containment of the terminal module in the first core identifies its
commutator with the initial center as the first center. For the actual
`GeneratedNeighborhoodV` definition, the initial-orbit center/module
identity also identifies each neighboring W with its V and U with the
initial W. This proves the second equality of the required commutator
dichotomy without any terminal containment assumption.

These identities do not assert the terminal commutator bound or any of the
forbidden normality outcomes. Source: printed p.54 / PDF p.44 of
`refs/files/stellmacher-n-group.pdf`, the paragraph beginning "Assume that U".
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_seven_commutator_eq_first_center_of_terminal_module_le_first_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hstartCard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hendCard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 3)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep) :
    ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep ∧
    ZAt ctx.Γ ctx.criticalPath.firstStep ≤ ZAt ctx.Γ ctx.criticalPath.a := by
  have hcomm := nine_initial_next_core_commutator_of_initial_four
    ctx.toLocalContext hstartCard
  have hbound : ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl hcore).trans_eq hcomm
  refine ⟨Subgroup.eq_of_le_of_card_ge hbound ?_, ?_⟩
  · have hfirstCard : Nat.card (ZAt ctx.Γ ctx.criticalPath.firstStep) = 2 :=
      nine_next_center_order_of_initial_four ctx.toLocalContext hstartCard
    rw [nine_seven_terminal_initial_commutator_card_two ctx hb hstartCard hendCard,
      hfirstCard]
  · change z ctx.Γ ctx.criticalPath.firstStep ≤ z ctx.Γ ctx.criticalPath.a
    rw [(lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).next_center.1]
    obtain ⟨_, sylow, hsylow⟩ := (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
    rw [z, ctx.Γ.zAt_def]
    exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩

end Stellmacher.SectionNine

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem nine_seven_neighbor_neighborhood_eq_module
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a) :
    GeneratedNeighborhoodV ctx.Γ neighbor = VAt ctx.Γ neighbor := by
  have hcenters (vertex : ctx.Γ.Vertex)
      (hvertex : vertex ∈ Neighborhood ctx.Γ neighbor) :
      ZAt ctx.Γ vertex = VAt ctx.Γ vertex := by
    have hinitial : ctx.criticalPath.a ∈ Neighborhood ctx.Γ neighbor :=
      (mem_neighborhood_iff_adjacent ctx.Γ).mpr
        (ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor))
    obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
      neighbor hinitial hvertex
    exact (nine_seven_center_join ctx vertex ⟨actor, hactor⟩).1
  change sSup {subgroup : Subgroup G | ∃ vertex, vertex ∈ Neighborhood ctx.Γ neighbor ∧
    subgroup = VAt ctx.Γ vertex} = ctx.Γ.vAt neighbor
  rw [ctx.Γ.vAt_def]
  congr 1
  ext subgroup
  constructor
  · rintro ⟨vertex, hvertex, rfl⟩
    exact ⟨vertex, hvertex, (hcenters vertex hvertex).symm⟩
  · rintro ⟨vertex, hvertex, rfl⟩
    exact ⟨vertex, hvertex, hcenters vertex hvertex⟩

public theorem nine_seven_initial_neighbor_join_eq_neighborhood
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) :
    sSup {subgroup : Subgroup G | ∃ neighbor,
      neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
        subgroup = GeneratedNeighborhoodV ctx.Γ neighbor} =
      GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a := by
  unfold GeneratedNeighborhoodV
  congr 1
  ext subgroup
  constructor
  · rintro ⟨neighbor, hneighbor, rfl⟩
    exact ⟨neighbor, hneighbor, nine_seven_neighbor_neighborhood_eq_module ctx neighbor hneighbor⟩
  · rintro ⟨neighbor, hneighbor, rfl⟩
    exact ⟨neighbor, hneighbor,
      (nine_seven_neighbor_neighborhood_eq_module ctx neighbor hneighbor).symm⟩

public theorem nine_seven_terminal_contained_commutator_dichotomy
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) :
    ⁅GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a, VAt ctx.Γ ctx.criticalPath.a'⁆ =
        ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ ∨
      ⁅sSup {subgroup : Subgroup G | ∃ neighbor,
        neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
          subgroup = GeneratedNeighborhoodV ctx.Γ neighbor}, VAt ctx.Γ ctx.criticalPath.a'⁆ =
        ⁅GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a, VAt ctx.Γ ctx.criticalPath.a'⁆ := by
  exact Or.inr (congrArg (fun subgroup : Subgroup G =>
    ⁅subgroup, VAt ctx.Γ ctx.criticalPath.a'⁆)
      (nine_seven_initial_neighbor_join_eq_neighborhood ctx))

end Stellmacher.SectionNine

module
public import Stellmacher.SectionNine.NineThreeSecondConfiguration

/-!
# Center inputs for the second geometric configuration in (9.3)

For the actual first and second extraction records, the first new vertex m
is conjugate to the initial vertex, while the first step is conjugate to
the terminal vertex. The second path vertex l neighbors the first step;
its center lies in the core at m and has the initial center's order. The
center at m centralizes its own core.

Endpoint alignment followed by the first residual conjugator gives the
first orbit assertion, and inverse alignment gives the second. Prepending
m to the reversed terminal-to-l path gives distance at most b-1, so critical
minimality puts Z_l in Q_m. Local transitivity at the first step conjugates
l with the initial vertex, preserving center order. The center-core
assertion of (7.3) gives centralization at m.

These are the geometric inputs for the second center-intersection argument
in Stellmacher (9.3), Journal of Algebra 190 (1997), p.49. Neither the
conclusion of (9.3) nor a distance-three specialization is assumed.
Source: `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

/-- The actual first and second extractions give the geometric and center
inputs for the repeated center-intersection argument in (9.3). -/
public theorem nine_three_second_center_inputs
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first) :
    let Γ := ctx.Γ
    let cp := ctx.criticalPath
    let m := Γ.act first.extraction.x⁻¹ first.l
    let l := second.l
    IsConjugateVertex Γ cp.a m ∧
      IsConjugateVertex Γ cp.a' cp.firstStep ∧
      l ∈ Neighborhood Γ cp.firstStep ∧
      ZAt Γ l ≤ QAt Γ m ∧
      Nat.card (ZAt Γ l) = Nat.card (ZAt Γ cp.a) ∧
      ZAt Γ m ≤ Subgroup.centralizer (QAt Γ m : Set G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act first.extraction.x⁻¹ first.l
  let l := second.l
  change IsConjugateVertex Γ cp.a m ∧ _
  have hbLocal : 1 < cp.length := hb
  obtain ⟨g, hga, hgnext⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hgm : Γ.act (g * first.extraction.x⁻¹) cp.a = m := by
    rw [Γ.act_mul, hga, ← first.penultimate]
  have hback : Γ.act g⁻¹ cp.a' = cp.firstStep := by
    rw [← hgnext, ← Γ.act_mul, mul_inv_cancel, Γ.act_one]
  have hl : l ∈ Neighborhood Γ cp.firstStep := by
    obtain ⟨bound, heq⟩ := second.second
    change second.l ∈ Neighborhood Γ cp.firstStep
    rw [heq]
    exact (nine_three_second_extraction_inputs ctx.toLocalContext hb).1
  have hm : m ∈ neighborhood Γ cp.a' := first.extraction.neighbor
  have hZlQm : ZAt Γ l ≤ QAt Γ m := by
    apply critical_minimality Γ cp
    rw [Γ.distance_symm]
    have hmadj : Γ.adjacent m cp.a' :=
      Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hm)
    have hd := neighbor_reverse_path_distance_le Γ cp m 2 cp.length
      (by omega) le_rfl (by simpa [cp.path_end] using hmadj)
    obtain ⟨bound, heq⟩ := second.second
    change Γ.distance m second.l < cp.length
    rw [heq]
    exact lt_of_le_of_lt hd (by omega)
  have haNeighbor : cp.a ∈ neighborhood Γ cp.firstStep :=
    (mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
  obtain ⟨actor, hactor⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
    cp.firstStep haNeighbor hl
  have hcard : Nat.card (ZAt Γ l) = Nat.card (ZAt Γ cp.a) := by
    change Nat.card (z Γ l) = Nat.card (z Γ cp.a)
    rw [← hactor, z_act, Subgroup.card_map_of_injective (MulAut.conj (actor : G)⁻¹).injective]
  have htermNeighbor : cp.a' ∈ neighborhood Γ m :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hm))
  have hcentral : ZAt Γ m ≤ Subgroup.centralizer (QAt Γ m : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core m cp.a' htermNeighbor).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  exact ⟨⟨g * first.extraction.x⁻¹, hgm⟩, ⟨g⁻¹, hback⟩,
    hl, hZlQm, hcard, hcentral⟩

end Stellmacher.SectionNine

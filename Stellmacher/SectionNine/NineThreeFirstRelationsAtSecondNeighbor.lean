module
public import Stellmacher.SectionNine.NineThreeSecondCenterRelations
public import Stellmacher.SectionNine.NineThreeInitialExtractionInputs

/-!
# First-extraction center relations at the second extracted neighbor

Retain the actual first and second geometric configurations of (9.3), with
initial center order greater than four. The first new center, intersected
with the second new vertex core, equals its intersection with the original
penultimate center. That intersection has index at most two inside the
second new stabilizer intersection, and the first new center escapes that
stabilizer.

The second center relations select an actor in the second new center outside
the first new stabilizer. Retarget only the actor field of the first
geometric record; its group, coatom, and residual conjugator stay fixed.
Mutual quadraticity from (7.5), the ambient module-centralizer bound from
(7.7)(b), and the orbit edge-centralizer theorem supply a fresh small fixed
subgroup for this base vertex. The forward path bound puts the penultimate
center in its core. Endpoint alignment preserves that center's order, and
(7.3) gives center/core centralization. Apply the generic center-intersection
argument to those actual inputs.

This proves the first relations anew after the source replaces the initial
vertex by the second extracted neighbor. Source: Stellmacher (9.3), journal
p.49, the replacement before (4), `refs/files/stellmacher-n-group.pdf`.
The old relation at the original initial vertex is not used as a substitute.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

/-- The first geometric extraction satisfies its center relations again at
the second extracted neighbor, with the original witnesses retained. -/
public theorem nine_three_first_relations_at_second_neighbor
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first) :
    let m := ctx.Γ.act first.extraction.x⁻¹ first.l
    let n := ctx.Γ.act second.extraction.x⁻¹ second.l
    ZAt ctx.Γ m ⊓ QAt ctx.Γ n = ZAt ctx.Γ m ⊓ ZAt ctx.Γ first.l ∧
      Nat.card (ZAt ctx.Γ m ⊓ GAt ctx.Γ n : Subgroup G) ≤
        2 * Nat.card (ZAt ctx.Γ m ⊓ QAt ctx.Γ n : Subgroup G) ∧
      ¬ ZAt ctx.Γ m ≤ GAt ctx.Γ n := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act first.extraction.x⁻¹ first.l
  let n := Γ.act second.extraction.x⁻¹ second.l
  let V := VAt Γ cp.firstStep
  have hbLocal : 1 < cp.length := hb
  have hn : n ∈ neighborhood Γ cp.firstStep := second.extraction.neighbor
  have ha : cp.a ∈ neighborhood Γ cp.firstStep :=
    (mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)
  have hnorbit : IsConjugateVertex Γ cp.a n := by
    obtain ⟨g, hg⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
      cp.firstStep ha hn
    exact ⟨g, hg⟩
  have hZnV : ZAt Γ n ≤ V := by
    change z Γ n ≤ v Γ cp.firstStep
    rw [v, Γ.vAt_def]
    exact le_sSup ⟨n, hn, rfl⟩
  have hZmV : ZAt Γ m ≤ VAt Γ cp.a' := by
    change z Γ m ≤ v Γ cp.a'
    rw [v, Γ.vAt_def]
    exact le_sSup ⟨m, first.extraction.neighbor, rfl⟩
  have hZnnot : ¬ ZAt Γ n ≤ GAt Γ m :=
    (nine_three_second_center_relations ctx hb hlarge first second).2.2
  obtain ⟨actor, haZn, haNot⟩ := Set.not_subset.mp hZnnot
  let data : NineThreeGeometricData Γ cp.a' first.l V first.E first.A0 actor :=
    { first.extraction with actor_outside := haNot }
  have hnback : cp.firstStep ∈ neighborhood Γ n :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hn))
  have hcentralizer : Subgroup.centralizer (V : Set G) ≤ QAt Γ n :=
    (le_inf (nine_three_next_module_centralizer_two ctx).2
      (Subgroup.centralizer_le hZnV)).trans
      (nine_three_orbit_edge_core_centralizer ctx.toLocalContext n hnorbit cp.firstStep hnback)
  have hquad : ⁅⁅ZAt Γ n, ZAt Γ m ⊓ GAt Γ n⁆, ZAt Γ m ⊓ GAt Γ n⁆ = ⊥ := by
    have hlong := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb
    have hYV : ZAt Γ m ⊓ GAt Γ n ≤ VAt Γ cp.a' := inf_le_left.trans hZmV
    exact bot_unique ((Subgroup.commutator_mono
      (Subgroup.commutator_mono hZnV hYV) hYV).trans_eq hlong.2.2)
  obtain ⟨W, hWm, hWn, hWl, hbound, _, _⟩ :=
    nine_three_geometric_small_fixed_subgroup ctx.toLocalContext n cp.a' first.l hnorbit
      V first.E first.A0 actor haZn hZnV data hquad hcentralizer
  have hl : first.l ∈ neighborhood Γ cp.a' := by
    rw [first.penultimate]
    exact (nine_three_initial_extraction_inputs ctx.toLocalContext hb).1
  have hVQ : V ≤ QAt Γ first.l := by
    rw [first.penultimate]
    exact (nine_three_initial_extraction_inputs ctx.toLocalContext hb).2.1
  have hZlQn : ZAt Γ first.l ≤ QAt Γ n := by
    apply critical_minimality Γ cp
    rw [Γ.distance_symm, first.penultimate]
    have hnadj : Γ.adjacent n cp.firstStep :=
      Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hn)
    have hd := neighbor_path_distance_le Γ cp n 1 (cp.length - 1)
      (by omega) (by omega) (by simpa [cp.path_first] using hnadj)
    exact lt_of_le_of_lt hd (by omega)
  have hZnC : ZAt Γ n ≤ Subgroup.centralizer (QAt Γ n : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core n cp.firstStep hnback).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hcardL : Nat.card (ZAt Γ first.l) = Nat.card (ZAt Γ cp.a) := by
    obtain ⟨g, hg, _⟩ := lemma_seven_five_endpoint_alignment
      ctx.sectionSeven Γ cp ctx.commutator_eq
    have hgl : Γ.act g cp.a = first.l := hg.trans first.penultimate.symm
    rw [← hgl]
    change Nat.card (z Γ (Γ.act g cp.a)) = _
    rw [z_act]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hlargeL : 4 < Nat.card (ZAt Γ first.l) := by rw [hcardL]; exact hlarge
  exact nine_three_geometric_center_intersections ctx n cp.a' first.l
    ⟨1, Γ.act_one _⟩ hl V first.E first.A0 hVQ actor (hZnV haZn) haZn hZnC
    hZlQn hlargeL data W hWm hWn hWl hbound

end Stellmacher.SectionNine

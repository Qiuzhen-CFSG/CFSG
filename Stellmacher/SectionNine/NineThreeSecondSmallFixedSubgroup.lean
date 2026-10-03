module
public import Stellmacher.SectionNine.NineThreeSecondConfiguration
public import Stellmacher.SectionNine.NineThreeGeometricSmallFixedSubgroup
public import Stellmacher.SectionNine.NineThreeOrbitModuleCentralizer
public import Stellmacher.SectionNine.NineThreeOrbitEdgeCoreCentralizer

/-!
# The small fixed subgroup for the second extraction

Retain both actual geometric configurations of (9.3). The second new
center has a subgroup W in its intersection with the first extracted
stabilizer of index at most two. W lies in the first extracted core and
the second path center, and the second extracted group centralizes it.
The fixed space of W in the first extracted center escapes the second
new stabilizer.

Endpoint alignment and the first conjugator place the first extracted
vertex in the initial orbit. The mutual quadratic action of (7.5) supplies
the required action hypothesis. Transport the ambient module-centralizer
containment to the terminal vertex, and use the orbit edge-centralizer
identity to put that centralizer in the first extracted core. The generic
geometric fixed-subgroup theorem then gives all assertions for the actual
second witnesses. No replacement CriticalPath or new commutation premise
is assumed.

Source: Stellmacher (9.3), Journal of Algebra 190 (1997), p.49, 'the same
argument as above', `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_second_small_fixed_subgroup
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first) :
    let m := ctx.Γ.act first.extraction.x⁻¹ first.l
    let n := ctx.Γ.act second.extraction.x⁻¹ second.l
    ∃ W : Subgroup G, W ≤ ZAt ctx.Γ n ∧ W ≤ QAt ctx.Γ m ∧
      W ≤ ZAt ctx.Γ second.l ∧
      Nat.card (ZAt ctx.Γ n ⊓ GAt ctx.Γ m : Subgroup G) ≤ 2 * Nat.card W ∧
      second.E ≤ Subgroup.centralizer (W : Set G) ∧
      ¬ ZAt ctx.Γ m ⊓ Subgroup.centralizer (W : Set G) ≤ GAt ctx.Γ n := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act first.extraction.x⁻¹ first.l
  let n := Γ.act second.extraction.x⁻¹ second.l
  let Y := ZAt Γ n ⊓ GAt Γ m
  have hmorbit : IsConjugateVertex Γ cp.a m := by
    obtain ⟨g,hg,_⟩ := lemma_seven_five_endpoint_alignment ctx.sectionSeven Γ cp ctx.commutator_eq
    refine ⟨g * first.extraction.x⁻¹, ?_⟩
    rw [Γ.act_mul,hg,← first.penultimate]
  have hZmV : ZAt Γ m ≤ VAt Γ cp.a' := by
    change z Γ m ≤ v Γ cp.a'
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨m,first.extraction.neighbor,rfl⟩
  have hZnV : ZAt Γ n ≤ VAt Γ cp.firstStep := by
    change z Γ n ≤ v Γ cp.firstStep
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨n,second.extraction.neighbor,rfl⟩
  have hYV : Y ≤ VAt Γ cp.firstStep := inf_le_left.trans hZnV
  have hquad : ⁅⁅ZAt Γ m,Y⁆,Y⁆ = ⊥ := by
    have hq := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb
    exact bot_unique ((Subgroup.commutator_mono
      (Subgroup.commutator_mono hZmV hYV) hYV).trans_eq hq.2.1)
  have hendOrbit : IsConjugateVertex Γ cp.firstStep cp.a' := by
    obtain ⟨g,_,hg⟩ := lemma_seven_five_endpoint_alignment ctx.sectionSeven Γ cp ctx.commutator_eq
    exact ⟨g,hg⟩
  have hCcore : Subgroup.centralizer (VAt Γ cp.a' : Set G) ≤ QAt Γ cp.a' :=
    nine_three_module_centralizer_core_at_vertex ctx cp.a' hendOrbit
  have hmback : cp.a' ∈ neighborhood Γ m :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp first.extraction.neighbor))
  have hcentralizer : Subgroup.centralizer (VAt Γ cp.a' : Set G) ≤ QAt Γ m :=
    (le_inf hCcore (Subgroup.centralizer_le hZmV)).trans
      (nine_three_orbit_edge_core_centralizer ctx.toLocalContext m hmorbit cp.a' hmback)
  exact nine_three_geometric_small_fixed_subgroup ctx.toLocalContext m cp.firstStep second.l
    hmorbit (VAt Γ cp.a') second.E second.A0 second.actor second.actor_first_center hZmV
    second.extraction hquad hcentralizer

end Stellmacher.SectionNine

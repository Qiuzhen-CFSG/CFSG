module
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortGirth
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Locally injective maps into trees

A graph homomorphism from a connected graph into an acyclic graph is injective
if it is injective on every neighbor set. Join two vertices by a simple path.
Its image is nonbacktracking by local injectivity, hence is a path by acyclicity.
Equal endpoint images force its length, and therefore the original path length,
to be zero.

This is the graph embedding step in Goldschmidt, *Automorphisms of trivalent
graphs* (1980), (2.6), printed pp.380--381: the coset graph of the groups generated
at adjacent vertices maps locally injectively into the original tree.
-/

@[expose] public section
namespace SimpleGraph
variable {V W : Type*} {Γ : SimpleGraph V} {Δ : SimpleGraph W}

/-- A connected graph mapping locally injectively into an acyclic graph
embeds on vertices. -/
theorem Hom.injective_of_locally_injective_of_acyclic (f : Γ →g Δ)
    (hΓ : Γ.Connected) (hΔ : Δ.IsAcyclic)
    (hf : ∀ v, Function.Injective (f.mapNeighborSet v)) : Function.Injective f := by
  intro x y hxy
  obtain ⟨p, hp⟩ := hΓ.exists_isPath x y
  let q := (BasedWalk.ofWalk p).map f
  have hq : q.Nonbacktracking :=
    (BasedWalk.nonbacktracking_map_iff f hf _).mpr
      (BasedWalk.nonbacktracking_ofWalk_of_isPath p hp)
  have hpath : q.toWalk.IsPath :=
    PathTransitivePolygon.isPath_of_nonbacktracking_of_cycle_bound
      (N := p.length) (fun v c hc => (hΔ c hc).elim) q hq le_rfl
  have hend : q.endpoint = f x := by
    rw [BasedWalk.endpoint_map, BasedWalk.endpoint_ofWalk, hxy]
  have hl := (hpath.nil_iff_eq.mpr hend.symm).length_eq_zero
  rw [BasedWalk.length_toWalk] at hl
  exact Walk.eq_of_length_eq_zero hl

end SimpleGraph

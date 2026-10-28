module

public import Theory.Representation.G2BinaryHyperplaneFixers
public import Theory.Representation.G2OrthogonalCover

/-!
# Pointwise fixers of large subspaces in the binary G₂ cover

A subspace missing the scalar identity projects injectively to the natural
six-space. If it has dimension at least five, its pointwise fixer in the full
G₂ model is therefore trivial by the natural involution rank bound.

This is the model input for the local-centralizer and Sylow preparation in
Aschbacher--Smith, Lemma 12.4.8, printed p.815. It applies both to a cover
hyperplane and to a hyperplane of that hyperplane.
-/

public section
open Module Submodule LinearMap
namespace Atlas.G2.Natural.OrthogonalCover
local notation "F" => ZMod 2
local notation "E" => TraceZero F

theorem pointwise_large_subspace_trivial (U : Submodule F E)
    (hU : 5 ≤ finrank F U) (hi : identity F ∉ U) (g : Model F)
    (hfix : ∀ x ∈ U, traceZeroAction F g x = x) : g = 1 := by
  let q := (mk F).domRestrict U
  have hq : Function.Injective q := by
    apply LinearMap.injective_domRestrict_iff.mpr
    rw [mk, Submodule.ker_mkQ]
    exact Submodule.disjoint_span_singleton_of_notMem hi
  let c := Restricted.NaturalCoordinates.equiv F
  let W := q.range.map c.toLinearMap
  have hdim : 5 ≤ finrank F W := by
    rw [c.finrank_map_eq, LinearMap.finrank_range_of_inj hq]
    exact hU
  apply BinaryNondegeneratePlane.pointwise_large_subspace_trivial W hdim
  intro y hy
  obtain ⟨z, ⟨x, rfl⟩, rfl⟩ := hy
  have he := LinearMap.congr_fun
    ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' g) (q x)
  change c (Natural.action F g (mk F x.val)) =
    BinaryNondegeneratePlane.rho g (c (q x)) at he
  rw [action_mk, hfix x.val x.property] at he
  exact he.symm

end Atlas.G2.Natural.OrthogonalCover

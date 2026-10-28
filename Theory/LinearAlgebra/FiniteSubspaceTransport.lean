module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Moving a small subspace into a prescribed subspace

An injection between two finite-dimensional subspaces extends to an ambient
automorphism after identifying its range. Consequently a finite set of vectors
can be moved into any subspace whose dimension is at least the size of that set.

This is the linear-algebra step in Aschbacher, *Sporadic Groups* (1994),
Example 38.4: the three points of a triangle lie in a translate of a fixed
projective plane. No transitivity on ordered triples is assumed.
-/

public section
namespace Submodule
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- A subspace can be moved into any subspace of at least its dimension. -/
theorem exists_linearEquiv_mapsTo_of_finrank_le (W P : Submodule K V)
    (h : Module.finrank K W ≤ Module.finrank K P) :
    ∃ g : V ≃ₗ[K] V, ∀ w ∈ W, g w ∈ P := by
  obtain ⟨f, hf⟩ := finrank_le_iff_exists_linearMap.mp h
  let f' := P.subtype.comp f
  have hf' : Function.Injective f' := Subtype.val_injective.comp hf
  obtain ⟨g, hg⟩ := exists_linearEquiv_restrict_eq (LinearEquiv.ofInjective f' hf')
  refine ⟨g, fun w hw => ?_⟩
  have he := hg ⟨w, hw⟩
  change (f ⟨w, hw⟩ : V) = g w at he
  rw [← he]
  exact (f ⟨w, hw⟩).property

/-- A finite set fits into a translate of a subspace of sufficiently large dimension. -/
theorem exists_linearEquiv_finset_mem (P : Submodule K V) (s : Finset V)
    (h : s.card ≤ Module.finrank K P) :
    ∃ g : V ≃ₗ[K] V, ∀ v ∈ s, g v ∈ P := by
  obtain ⟨g, hg⟩ := exists_linearEquiv_mapsTo_of_finrank_le (span K (s : Set V)) P
    ((finrank_span_finset_le_card s).trans h)
  exact ⟨g, fun v hv => hg v (subset_span hv)⟩

end Submodule

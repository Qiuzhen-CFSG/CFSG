module

public import Theory.AlgebraicGroup.RootSubgroups.Finite

/-!
This module supplies the finite indexing list used by the invariant-unipotent
ordered-product bridge.  For a realized root-group datum, injectivity of
`rootWeight` transports finiteness of the ambient torus-root set to the roots
whose root subgroups lie in a chosen closed subgroup.  Enumerating that finite
set with `Finset.toList` gives the required nodup list and membership
equivalence.  The finiteness input is `torusRootSet_finite`, proved from the
finite weight set of the identity tangent representation; this is the
finite-root input in the GLS3 Chapter 1, Section 1.9 development.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The realized roots whose root subgroups are contained in `X`, listed
without duplicates. -/
public theorem finite_contained_root_list
    {K : Variety k} [AlgebraicGroup K]
    (T X : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization) :
    ∃ roots : List D.Root,
      roots.Nodup ∧ ∀ α, α ∈ roots ↔ D.rootSubgroup α ≤ X := by
  have hfiniteWeights : (TorusRootSet T).Finite := torusRootSet_finite T
  have hfiniteRoot : Set.Finite {α : D.Root | D.rootSubgroup α ≤ X} := by
    apply Set.Finite.of_finite_image (f := D.rootWeight)
    · apply hfiniteWeights.subset
      intro χ hχ
      rcases hχ with ⟨α, hα, rfl⟩
      rw [← hD.2.1]
      exact ⟨α, rfl⟩
    · exact hD.1.injOn
  let roots : List D.Root := hfiniteRoot.toFinset.toList
  refine ⟨roots, ?_, ?_⟩
  · exact Finset.nodup_toList _
  · intro α
    change α ∈ hfiniteRoot.toFinset.toList ↔
      α ∈ {β : D.Root | D.rootSubgroup β ≤ X}
    rw [Finset.mem_toList, hfiniteRoot.mem_toFinset]

end Theory.AlgebraicGroup

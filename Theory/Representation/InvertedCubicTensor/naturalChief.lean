module
public import Theory.Representation.InvertedCubicTensor
public import Theory.Representation.SubrepresentationLattice

/-!
# The binary natural S₃ constituent

The cubic cycles the three nonzero vectors of the concrete permutation
core. Every nonzero invariant subspace therefore contains the whole plane;
the same explicit cubic moves a vector. These give the irreducibility and
noncentrality required by chief refinement, without assuming either.

Source application: Aschbacher--Smith, 13.7.10(8), printed p.942.
-/

public section
namespace InvertedCubicTensor
private instance coreFintype : Fintype (BinaryPermutation.core (Fin 3)) :=
  @Subtype.fintype _ _
    (fun x => inferInstanceAs (Decidable (∑ i : Fin 3, x i = 0)))
    (inferInstance : Fintype (Fin 3 → ZMod 2))

private theorem natural_transitive :
    ∀ u v : BinaryPermutation.core (Fin 3), u ≠ 0 → v ≠ 0 →
      ∃ g : S₃, BinaryPermutation.coreRepresentation (Fin 3) g u = v := by
  intro u v hu hv
  have cert : ∀ u v : BinaryPermutation.core (Fin 3), u ≠ 0 → v ≠ 0 →
      v = u ∨ v = BinaryPermutation.coreRepresentation (Fin 3) cubic u ∨
      v = BinaryPermutation.coreRepresentation (Fin 3) (cubic*cubic) u := by
    decide +kernel
  rcases cert u v hu hv with he | he | he
  · exact ⟨1, by simpa using he.symm⟩
  · exact ⟨cubic, he.symm⟩
  · exact ⟨cubic*cubic, he.symm⟩

theorem natural_irreducible : Representation.IsIrreducible (BinaryPermutation.coreRepresentation (Fin 3)) := by
  classical
  have hnt : Nontrivial (BinaryPermutation.core (Fin 3)) := by
    apply Module.nontrivial_of_finrank_pos (R := ZMod 2)
    rw [natural_finrank]
    decide
  refine ⟨fun P => ?_⟩
  by_cases hp : P.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hp)
  right
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro v _
  by_cases hv : v = 0
  · subst v
    exact P.toSubmodule.zero_mem
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  obtain ⟨g, rfl⟩ := natural_transitive u v hu0 hv
  exact P.apply_mem_toSubmodule g hu

theorem natural_noncentral :
    ∃ g v, BinaryPermutation.coreRepresentation (Fin 3) g v ≠ v := by
  refine ⟨cubic, ⟨![1,1,0], by change ∑ i : Fin 3, (![1,1,0] : Fin 3 → ZMod 2) i = 0; decide⟩, ?_⟩
  decide +kernel
end InvertedCubicTensor

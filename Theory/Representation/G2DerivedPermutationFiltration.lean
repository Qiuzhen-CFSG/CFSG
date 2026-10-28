module

public import Theory.Representation.G2DerivedPermutationFiltration.Incidence
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations
public import Theory.Representation.G2DerivedPermutationFiltration.Extensions

/-!
# The binary derived G₂ permutation filtration

The actual commutator subgroup of the split-octonion G₂(2) acts transitively
on 189 unipotent cosets, with a two-group stabilizer of order 32. The binary
incidence boundary maps this flag module to the two 63-point parabolic modules.
Their checked filtrations have simple factors of degrees 1, 6 and 14; the
literal boundary kernel has two simple factors of degree 32.

Pulling back the product filtration along the boundary and adjoining the
kernel filtration therefore gives an actual filtration of the flag module.
Every simple factor has degree 1, 6 or greater than 8. The exported witnesses
supply the concrete permutation-filtration input for the small-degree argument
in Aschbacher–Smith G.7.2(3), printed pp.347–348 / PDF pp.358–359. The comparison
with PSU₃(3) and assembly of that source theorem belong to its consumer.
-/

public section

namespace G2DerivedPermutationFiltration

/-- The two actual parabolic modules together have only allowed simple factors. -/
theorem vertexPair_factorDegreeFiltration :
    Representation.FactorDegreeFiltration allowedDegrees vertexPairRepresentation :=
  (vertex_factorDegreeFiltration 0).prod (vertex_factorDegreeFiltration 1)

/-- The actual 189-dimensional unipotent-coset module has a finite filtration
by invariant subspaces whose literal simple quotients have allowed degrees. -/
theorem flag_factorDegreeFiltration :
    Representation.FactorDegreeFiltration allowedDegrees flagRepresentation :=
  Representation.FactorDegreeFiltration.of_ker boundary
    cycle_factorDegreeFiltration vertexPair_factorDegreeFiltration

/-- Concrete witnesses for the permutation-filtration input to G.7.2(3).
The acting group is literally the commutator subgroup of the octonion model. -/
theorem exists_permutation_filtration :
    ∃ (Ω : Type) (_ : Fintype Ω) (τ : Group →* Equiv.Perm Ω) (o : Ω) (H : Subgroup Group),
      IsPGroup 2 H ∧
      (∀ g, g ∈ H ↔ τ g o = o) ∧
      (∀ x, ∃ g, τ g o = x) ∧
      Representation.FactorDegreeFiltration {d : ℕ | d = 1 ∨ d = 6 ∨ 8 < d}
        ((BinaryPermutation.representation Ω).comp τ) :=
  ⟨Flag, inferInstance, flagPerm, baseFlag, flagStabilizer, flagStabilizer_isPGroup,
    mem_flagStabilizer_iff, flagTransitive, flag_factorDegreeFiltration⟩

end G2DerivedPermutationFiltration

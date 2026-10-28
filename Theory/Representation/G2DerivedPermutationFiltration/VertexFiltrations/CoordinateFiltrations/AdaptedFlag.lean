module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.Interface
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.AdaptedFlag.MatrixChecks
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.AdaptedFlag.Construction

/-!
# Certified adapted flags for both binary vertex actions

The two published 63-dimensional free-group representations have invariant
flags with respectively nine and twelve successive quotients. Each literal
quotient is linearly isomorphic to its displayed block of binary coordinates,
intertwining both generators with the corresponding `factorMatrix`.

The matrix certificates prove the adapted-basis identities and preservation
of the initial segments. The quotient construction identifies each block
projection's kernel with the preceding stage. Together they discharge every
field of `FlagCoordinates` without an additional mathematical premise.

This is the coordinate ingredient for Aschbacher–Smith G.7.2(3), printed
pp.347–348. Simplicity of the factors and identification of the ambient group
are separate ingredients of the source-theorem assembly.
-/

@[expose] public section

namespace G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

/-- The invariant flag and literal quotient coordinates obtained from the
published adapted basis, for either of the two permutation representations. -/
noncomputable def adaptedFlagCoordinates (i : Fin 2) : FlagCoordinates i :=
  AdaptedFlag.flagCoordinates i (AdaptedFlag.basisCoordinates i)
    (AdaptedFlag.basisCoordinates_generator i) (AdaptedFlag.upper i)

/-- Both published binary representations admit the required equivariant
coordinate isomorphisms on every literal successive quotient. -/
theorem nonempty_flagCoordinates : ∀ i : Fin 2, Nonempty (FlagCoordinates i) :=
  fun i => ⟨adaptedFlagCoordinates i⟩

end G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

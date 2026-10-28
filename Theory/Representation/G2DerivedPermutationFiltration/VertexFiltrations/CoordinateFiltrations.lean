module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.Coordinates
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.Interface
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.AdaptedFlag
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.Density

/-!
# The two binary coordinate filtrations

The checked adapted bases give two invariant flags in the actual free-group
permutation representations on 63 binary coordinates. Their successive
quotient dimensions are respectively
`[14, 6, 1, 6, 14, 1, 6, 14, 1]` and
`[6, 14, 1, 6, 1, 6, 14, 1, 6, 1, 6, 1]`.

Equivariant coordinates identify each literal quotient action with its
displayed diagonal matrices. The matrix-algebra certificates then prove
irreducibility, so the finite flags yield unconditional factor-degree
filtrations. This is the coordinate ingredient for Aschbacher–Smith G.7.2(3),
printed pp.347–348; identification with the ambient parabolic actions belongs
to the vertex-filtration assembly.
-/

@[expose] public section

namespace G2DerivedPermutationFiltration.VertexCoordinates

namespace CoordinateFiltrations

/-- Every literal successive quotient of the checked adapted flag is simple. -/
theorem adaptedFlag_quotient_irreducible (i : Fin 2) (t : Factor i) :
    Representation.IsIrreducible
      (within ((adaptedFlagCoordinates i).stage t.val)
        ((adaptedFlagCoordinates i).stage (t.val + 1))).quotientRepresentation :=
  irreducible_of_coordinate_matrices (degree_pos i t) FreeGroup.of
    (factorMatrix i t) ((adaptedFlagCoordinates i).coordinates t)
    ((adaptedFlagCoordinates i).generator_coordinates t) (factorMatrix_algebra_eq_top i t)

/-- The dimension of each literal quotient is its published block degree. -/
theorem adaptedFlag_quotient_finrank (i : Fin 2) (t : Factor i) :
    Module.finrank (ZMod 2)
      (((adaptedFlagCoordinates i).stage (t.val + 1)).toSubmodule ⧸
        (within ((adaptedFlagCoordinates i).stage t.val)
          ((adaptedFlagCoordinates i).stage (t.val + 1))).toSubmodule) = degree i t := by
  simpa only [Module.finrank_fin_fun] using
    ((adaptedFlagCoordinates i).coordinates t).finrank_eq

end CoordinateFiltrations

open CoordinateFiltrations

/-- Both explicit binary coordinate actions have a finite invariant filtration
with irreducible factors of degrees one, six, or greater than eight. -/
theorem coordinate_factorDegreeFiltration (i : Fin 2) :
    Representation.FactorDegreeFiltration allowedDegrees (representation i) :=
  filtration_of_certificates i (adaptedFlagCoordinates i) (factorMatrix_algebra_eq_top i)

end G2DerivedPermutationFiltration.VertexCoordinates

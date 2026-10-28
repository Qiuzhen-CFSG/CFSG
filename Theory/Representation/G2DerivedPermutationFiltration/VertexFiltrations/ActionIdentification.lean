module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.Generators
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.ActionIdentification.Geometry
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.ActionIdentification.Generation

/-!
# Identification of the two binary derived G₂ coset actions

The published root words generate the actual commutator subgroup of G₂(2).
The published representatives biject with both ambient parabolic coset spaces,
and the two generator tables give their actual left actions. The geometric
certificates and the sixteen two-coset Schreier identities are kernel checked
in the imported modules. This supplies the action identification used for the
parabolic module filtrations supporting Aschbacher–Smith G.7.2(3), p.348.
-/

public section

namespace G2DerivedPermutationFiltration.VertexCoordinates

/-- Each literal GAP right-coset Schreier product lies in the corresponding
ambient parabolic. Inversion gives the published left-action equation. -/
theorem schreier_mem_parabolic (i j : Fin 2) (x : Fin 63) :
    evalWord (representativeWord i x) * evalWord (generatorWord j) *
      (evalWord (representativeWord i (generator i j x)))⁻¹ ∈ parabolic i :=
  (vertex_generator_action_iff i j x).mp (vertex_generator_action i j x).symm

end G2DerivedPermutationFiltration.VertexCoordinates

module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.CoordinateInterface
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCriterion
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.ModelLink
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.FactorAlgebras

/-!
# Assembly of the binary G₂ incidence-cycle filtration

The certified coset coordinates identify an actual invariant half of the
incidence kernel and its literal quotient with two 32-dimensional matrix
modules. Checked rank-one and orbit-basis identities prove that each pair of
action matrices generates the full matrix algebra.

Density makes the half and the literal quotient irreducible. Their coordinate
equivalences give dimension 32, so the zero/half/whole chain is a filtration
whose factor degrees belong to `allowedDegrees`.

Source application: Aschbacher–Smith G.7.2(3), printed p.348 / PDF p.359.
The unconditional `cycle_factorDegreeFiltration` discharges both inputs using
the concrete coordinate and matrix-algebra proofs. No Steinberg restriction
fact is assumed.
-/

public section

open Representation
namespace G2DerivedPermutationFiltration

namespace CycleCoordinates

/-- Density proves simplicity of the actual half, after its action has been linked. -/
theorem half_irreducible (c : CycleCoordinates) (h : CycleData.FullFactorAlgebra 0) :
    IsIrreducible (k := ZMod 2) (G := Group) (V := c.half.toSubmodule) c.half.toRepresentation :=
  CycleMatrixCriterion.subspace_irreducible_of_coordinate_matrices
    (k := ZMod 2) (G := Group) (V := cycleSubrepresentation.toSubmodule) (n := Fin 32)
    cycleSubrepresentation.toRepresentation c.half
    c.subspaceCoordinates (c.actor 0) (c.actor 1)
    (CycleData.factorMatrix 0 0) (CycleData.factorMatrix 0 1)
    (c.subspace_action 0) (c.subspace_action 1) h

/-- Simplicity is proved for the literal quotient, not for an unrelated matrix module. -/
theorem quotient_irreducible (c : CycleCoordinates) (h : CycleData.FullFactorAlgebra 1) :
    IsIrreducible (k := ZMod 2) (G := Group)
      (V := cycleSubrepresentation.toSubmodule ⧸ c.half.toSubmodule) c.half.quotientRepresentation :=
  CycleMatrixCriterion.irreducible_of_coordinate_matrices (k := ZMod 2) (G := Group)
    (V := cycleSubrepresentation.toSubmodule ⧸ c.half.toSubmodule) (n := Fin 32)
    c.half.quotientRepresentation
    c.quotientCoordinates (c.actor 0) (c.actor 1)
    (CycleData.factorMatrix 1 0) (CycleData.factorMatrix 1 1)
    (c.quotient_action 0) (c.quotient_action 1) h

end CycleCoordinates

/-- Conditional final assembly. Both coordinate and finite-algebra inputs must
be discharged before this yields the requested cycle filtration. -/
theorem cycle_factorDegreeFiltration_of_coordinates_and_matrix_algebras
    (c : CycleCoordinates) (h : ∀ f : Fin 2, CycleData.FullFactorAlgebra f) :
    FactorDegreeFiltration allowedDegrees cycleSubrepresentation.toRepresentation := by
  apply FactorDegreeFiltration.step c.half
  · apply CycleMatrixCriterion.simple_filtration (k := ZMod 2) (G := Group) (V := c.half.toSubmodule)
      allowedDegrees c.half.toRepresentation
      (c.half_irreducible (h 0))
    rw [c.finrank_half]
    exact Or.inr (Or.inr (by decide))
  · exact c.quotient_irreducible (h 1)
  · rw [c.finrank_quotient]
    exact Or.inr (Or.inr (by decide))

/-- The actual incidence kernel has two irreducible factors of degree 32,
so its factor degrees are allowed in the binary permutation filtration. -/
theorem cycle_factorDegreeFiltration :
    FactorDegreeFiltration allowedDegrees cycleSubrepresentation.toRepresentation :=
  cycle_factorDegreeFiltration_of_coordinates_and_matrix_algebras
    cycleCoordinates CycleData.fullFactorAlgebra

/-- The literal boundary kernel in the 189-dimensional flag module has dimension 64. -/
theorem finrank_cycleSpace :
    Module.finrank (ZMod 2) cycleSubrepresentation.toSubmodule = 64 :=
  cycleCoordinates.finrank_cycle

end G2DerivedPermutationFiltration

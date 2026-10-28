module

public import Theory.Representation.G2DerivedPermutationFiltration.Incidence
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixData

/-!
# The concrete coordinate obligation for the binary G₂ cycle space

The finite matrix calculation and the coset calculation can be proved
independently. Their common interface requires an actual invariant subspace of
the boundary kernel, coordinates on that subspace and its literal quotient,
and two actual derived-group elements acting by the proposed matrices.

No irreducibility or filtration is a field of this interface. In particular,
merely constructing the record's type proves no assertion about the cycle
space. The finite matrix-algebra proof supplies simplicity only after a
witness of this interface has been constructed from the coset action.

Source application: Aschbacher–Smith G.7.2(3), printed p.348 / PDF p.359.
-/

@[expose] public section

namespace G2DerivedPermutationFiltration

/-- Coordinates to be constructed from the actual incidence kernel.
The quotient here is the quotient of the cycle space by `half`, not a
separately stipulated 32-dimensional representation. -/
structure CycleCoordinates where
  half : Subrepresentation cycleSubrepresentation.toRepresentation
  subspaceCoordinates : half.toSubmodule ≃ₗ[ZMod 2] CycleData.Half
  quotientCoordinates : (cycleSubrepresentation.toSubmodule ⧸ half.toSubmodule) ≃ₗ[ZMod 2] CycleData.Half
  actor : Fin 2 → Group
  subspace_action (a : Fin 2) :
    LinearMap.toMatrix' (subspaceCoordinates.conj (half.toRepresentation (actor a))) =
      CycleData.factorMatrix 0 a
  quotient_action (a : Fin 2) :
    LinearMap.toMatrix' (quotientCoordinates.conj (half.quotientRepresentation (actor a))) =
      CycleData.factorMatrix 1 a

namespace CycleCoordinates

theorem finrank_half (c : CycleCoordinates) : Module.finrank (ZMod 2) c.half.toSubmodule = 32 := by
  rw [c.subspaceCoordinates.finrank_eq]
  simp [CycleData.Half]

theorem finrank_quotient (c : CycleCoordinates) :
    Module.finrank (ZMod 2) (cycleSubrepresentation.toSubmodule ⧸ c.half.toSubmodule) = 32 := by
  rw [c.quotientCoordinates.finrank_eq]
  simp [CycleData.Half]

/-- A coordinate witness also certifies the entire cycle-space dimension. -/
theorem finrank_cycle (c : CycleCoordinates) :
    Module.finrank (ZMod 2) cycleSubrepresentation.toSubmodule = 64 := by
  have h := c.half.toSubmodule.finrank_quotient_add_finrank
  rw [c.finrank_quotient, c.finrank_half] at h
  exact h.symm

end CycleCoordinates
end G2DerivedPermutationFiltration

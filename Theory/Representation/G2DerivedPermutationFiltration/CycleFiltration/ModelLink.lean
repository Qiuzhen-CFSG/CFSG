module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.CoordinateInterface
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.ModelLink.Half

/-!
# Linking the concrete cycle calculation to the coordinate interface

The incidence module fixes the carrier of the cycle space as the literal
kernel of the two endpoint maps. The certified flag enumeration identifies
this kernel with the numerical cycle space. Pulling back the certified half
and its quotient coordinates gives the actual subspace and literal quotient.
The two actual derived-group generators have the prescribed action matrices;
their established generation theorem makes the half invariant for the whole
derived group.

The two fields of `CycleGeometryWitness` are deliberately actual linear
equivalences on the literal kernel and its literal quotient.  In particular,
the record cannot be filled by a dimension equality or by a separately
stipulated copy of a representation.  `CycleMatrixWitness` then checks the
four displayed matrices against those equivalences. The independent assembly
interface is retained, and `cycleCoordinates_nonempty` now supplies an
unconditional witness of the public `CycleCoordinates` record.

Source application: Aschbacher--Smith G.7.2(3), printed p.348 / PDF p.359.
-/

@[expose] public section

namespace G2DerivedPermutationFiltration

/-- The geometric part of a concrete cycle-space calculation.

`half` is a subrepresentation of the actual restricted flag action.  Thus
its invariance is for every element of the actual derived group, rather than
only for the two finite matrices used to find the candidate basis.
-/
structure CycleGeometryWitness where
  half : Subrepresentation cycleSubrepresentation.toRepresentation
  subspaceCoordinates : half.toSubmodule ≃ₗ[ZMod 2] CycleData.Half
  quotientCoordinates :
    (cycleSubrepresentation.toSubmodule ⧸ half.toSubmodule) ≃ₗ[ZMod 2] CycleData.Half
  actor : Fin 2 → Group

/-- The numerical part of a cycle-space calculation, relative to an actual
geometric witness. -/
structure CycleMatrixWitness (g : CycleGeometryWitness) : Prop where
  subspace_action (a : Fin 2) :
    LinearMap.toMatrix' (g.subspaceCoordinates.conj (g.half.toRepresentation (g.actor a))) =
      CycleData.factorMatrix 0 a
  quotient_action (a : Fin 2) :
    LinearMap.toMatrix' (g.quotientCoordinates.conj
      (g.half.quotientRepresentation (g.actor a))) =
      CycleData.factorMatrix 1 a

namespace CycleGeometryWitness

/-- Turn the independent geometry and matrix certificates into the public
coordinate record. -/
def toCycleCoordinates (g : CycleGeometryWitness)
    (m : CycleMatrixWitness g) : CycleCoordinates :=
  { half := g.half
    subspaceCoordinates := g.subspaceCoordinates
    quotientCoordinates := g.quotientCoordinates
    actor := g.actor
    subspace_action := m.subspace_action
    quotient_action := m.quotient_action }

theorem cycleCoordinates_nonempty_of_witness
    (g : CycleGeometryWitness) (m : CycleMatrixWitness g) :
    Nonempty CycleCoordinates :=
  ⟨g.toCycleCoordinates m⟩

end CycleGeometryWitness

/-- The concrete half and quotient coordinates for the actual binary G₂
derived-group incidence kernel. -/
noncomputable def cycleCoordinates : CycleCoordinates where
  half := CycleModelLink.invariantHalf
  subspaceCoordinates := CycleModelLink.halfCoordinates
  quotientCoordinates := CycleModelLink.quotientCoordinates
  actor := VertexCoordinates.groupGenerator
  subspace_action := CycleModelLink.half_factorMatrix
  quotient_action := CycleModelLink.quotient_factorMatrix

/-- The cycle coordinate obligation is realized without additional premises. -/
theorem cycleCoordinates_nonempty : Nonempty CycleCoordinates :=
  ⟨cycleCoordinates⟩

end G2DerivedPermutationFiltration

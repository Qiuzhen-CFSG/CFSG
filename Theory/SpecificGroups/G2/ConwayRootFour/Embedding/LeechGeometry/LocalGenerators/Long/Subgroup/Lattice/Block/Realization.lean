module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.MatrixData
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Descent
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.MarkedComparison
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.ComparisonData
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.IcosianComparison
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.TetrahedralMarking

/-!
# Integral quaternion realization of the explicit Eisenstein block

The literal matrix group acts faithfully on the retained integral Leech lattice.
`IcosianComparison` proves both integral containments and right-quaternion
compatibility of the displayed comparison. `TetrahedralMarking` identifies the
actual rational scalar image in the retained A₅ with A₄. Combining these gives
unconditional `matrixToLeech` and `matrixMarking`, the exact central-sign
preimage, and commutation after the literal Leech central projection.

The rational comparison, its lattice membership criterion, and the transported
action of every matrix (in particular both source generators) remain accessible
for the graph-normalizer construction. The action uses inverse adjoints because
the source Gram convention is `A H A* = H`. This supplies the integral realization
input of `Block.latticeBlockOfMatrix`; identification of the matrix sign quotient
with SL₃(4) belongs to its independent quotient construction.

Source: John Bray, ATLAS `6L34G1-Ar6aB0`, for the explicit matrices and row Gram
form; Aschbacher, *Sporadic Groups* (1994), 49.2 and 49.5, for the marked block
consumer. The retained icosian comparison and scalar quotient are the attributed
ATLAS ports of Gerald Höhn.
-/

@[expose] public noncomputable section
open Matrix Atlas.Lattices Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block
open Realization

/-- The explicit rational comparison from six quaternion coordinates to the
retained Leech coordinates. -/
def matrixComparison : Space ≃ₗ[ℚ] RationalCoordinates :=
  quaternionComparison.trans icosianComparison

theorem matrixComparison_form (x y : Space) :
    rationalForm (matrixComparison x) (matrixComparison y) = form x y :=
  leechComparison_form quaternionComparison quaternionComparison_form x y

/-- Both integral containments, with the actual retained Leech lattice. -/
theorem matrixComparison_lattice (x : Space) :
    x ∈ lattice ↔ matrixComparison x ∈ rationalLeech :=
  leechComparison_lattice quaternionComparison quaternionComparison_lattice x

/-- The comparison is the product of the two displayed coordinate matrices. -/
theorem matrixComparison_apply (x : Space) :
    matrixComparison x =
      (icosianComparisonMatrix * comparisonCandidateMatrix) *ᵥ x := by
  change icosianComparison (quaternionComparison x) = _
  rw [icosianComparison_apply, quaternionComparison_coordinates, Matrix.mulVec_mulVec]

/-- Faithful integral realization of the literal Eisenstein matrix group. -/
def matrixToLeech : matrixGroup →* LeechIsometryGroup :=
  toLeechOfIcosianComparison quaternionComparison
    quaternionComparison_form quaternionComparison_lattice

theorem matrixToLeech_injective : Function.Injective matrixToLeech :=
  quaternionComparison_toLeech_injective

/-- Exactly the original matrix signs become central Leech signs. -/
theorem matrixToLeech_signs : leechCentralSigns.comap matrixToLeech = matrixSigns :=
  quaternionComparison_toLeech_signs

theorem matrixToLeech_eq_negation (g : matrixGroup) :
    matrixToLeech g = negationIsometry ↔ g.val = -1 :=
  toLeechOfComparison_eq_negation _ _ _ g

/-- The rational extension is conjugation of the original faithful action. -/
theorem matrixToLeech_extension (g : matrixGroup) :
    (fullIsometryEquiv (matrixToLeech g)).val = comparedAction matrixComparison g :=
  toLeechOfComparison_extension _ _ _ g

/-- Evaluation retains the source inverse-adjoint convention. -/
theorem matrixToLeech_intertwines (g : matrixGroup) (x : Space) :
    (fullIsometryEquiv (matrixToLeech g)).val (matrixComparison x) =
      matrixComparison (realification g.val.inv.conjTranspose *ᵥ x) := by
  rw [matrixToLeech_extension]
  change matrixComparison (linearAction g (matrixComparison.symm (matrixComparison x))) = _
  rw [matrixComparison.symm_apply_apply]
  rfl

/-- Evaluation on an actual integral Leech vector, through the displayed
comparison and inverse-adjoint matrix. -/
theorem matrixToLeech_apply (g : matrixGroup) (x : leech) :
    rationalEmbedding ((matrixToLeech g).val x).val =
      matrixComparison (realification g.val.inv.conjTranspose *ᵥ
        matrixComparison.symm (rationalEmbedding x.val)) := by
  rw [← rationalExtension_agrees]
  change (fullIsometryEquiv (matrixToLeech g)).val (rationalEmbedding x.val) = _
  rw [matrixToLeech_extension]
  rfl

/-- The first source generator acts by the realification of its adjoint. -/
theorem matrixToLeech_generatorA (x : Space) :
    (fullIsometryEquiv (matrixToLeech
      ⟨generatorA, Subgroup.subset_closure (by simp)⟩)).val (matrixComparison x) =
      matrixComparison (realification matrixA.conjTranspose *ᵥ x) :=
  matrixToLeech_intertwines _ x

/-- The second source generator acts by the adjoint of the displayed inverse. -/
theorem matrixToLeech_generatorB (x : Space) :
    (fullIsometryEquiv (matrixToLeech
      ⟨generatorB, Subgroup.subset_closure (by simp)⟩)).val (matrixComparison x) =
      matrixComparison (realification matrixBInv.conjTranspose *ᵥ x) :=
  matrixToLeech_intertwines _ x

/-- The marking has the actual rational scalar image in the retained A₅. -/
def matrixMarking : alternatingGroup fourPoints →* alternatingGroup (Fin 5) :=
  rationalTetrahedralMarking

theorem matrixMarking_injective : Function.Injective matrixMarking :=
  rationalTetrahedralMarking_injective

theorem matrixMarking_range : matrixMarking.range = rationalScalarToFive.range :=
  rationalTetrahedralMarking_range

/-- Commutation already holds for the actual integral rational scalars. -/
theorem matrixToLeech_scalar (g : matrixGroup) (u : rationalScalarUnits) :
    Commute (matrixToLeech g) (icosianScalarsToCo0 u.val) :=
  quaternionComparison_toLeech_scalar g u

/-- The precise marked scalar commutation required by `latticeBlockOfMatrix`. -/
theorem matrixToLeech_commute (a : alternatingGroup fourPoints) (g : matrixGroup) :
    Commute (scalarFive (matrixMarking a)) (leechCentralProjection (matrixToLeech g)) :=
  toLeechOfIcosianComparison_commute quaternionComparison quaternionComparison_form
    quaternionComparison_lattice quaternionComparison_right matrixMarking matrixMarking_range a g

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block

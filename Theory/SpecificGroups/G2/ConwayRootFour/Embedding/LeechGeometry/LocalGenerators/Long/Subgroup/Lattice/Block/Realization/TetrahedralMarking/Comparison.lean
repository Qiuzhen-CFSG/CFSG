module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.TetrahedralMarking
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.MarkedComparison

/-!
# The rational tetrahedral marking in the literal Leech comparison

Apply the unconditional marking to the existing integral comparison consumer.
Its range equality discharges the finite scalar premise. The independent
isometric lattice comparison and rational right-linearity remain explicit;
no assertion of their existence is made here.

Source: Aschbacher, *Sporadic Groups* (1994), 49.2 and 49.5. The retained
icosian scalar and Leech comparison models are the attributed ATLAS ports.
-/

public noncomputable section
open Matrix Atlas.Algebra Atlas.Lattices Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization

/-- The actual A₄ marking centralizes the compared matrix action in the exact
Leech central quotient, under the independent marked lattice comparison. -/
theorem rationalTetrahedralMarking_commute
    (e : Space ≃ₗ[ℚ] IcosianRationalCoordinates)
    (heForm : ∀ x y, icosianBilinear (e x) (e y) = form x y)
    (heLattice : ∀ x, x ∈ lattice ↔ e x ∈ rationalIcosianLattice)
    (heRight : ∀ (a b c d : ℚ) (x : Space),
      e (rightScalar a b c d *ᵥ x) = icosianRightMul (e x) (scalarQuaternion a b c d))
    (a : alternatingGroup fourPoints) (g : matrixGroup) :
    Commute (scalarFive (rationalTetrahedralMarking a))
      (leechCentralProjection (toLeechOfIcosianComparison e heForm heLattice g)) :=
  toLeechOfIcosianComparison_commute e heForm heLattice heRight
    rationalTetrahedralMarking rationalTetrahedralMarking_range a g

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization

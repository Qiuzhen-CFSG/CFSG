module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitBound.Coordinates.Orbit

/-!
# Coordinates for the distinguished canonical homology orbit

The explicit column projection induces a linear equivalence from the literal
ker(a - 1)/im(a - 1) to twelve binary coordinates. Checked generator transitions
and paths identify its distinguished local-subgroup orbit with the 693 columns
of Geometry. Both directions are proved without additional hypotheses.

The splitting, action and orbit certificates are in the Coordinates descendants.
Source data and ATLAS attribution: ImageBound/source/README.md and
Coordinates/Tables.lean.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitGeometry

/-- Explicit coordinates on the canonical column homology quotient. -/
def orbitCoordinates : NaturalHomology ≃ₗ[ZMod 2] CoordinateSpace := Coordinates.equiv

/-- These coordinates identify exactly the actual distinguished local orbit. -/
theorem orbitCoordinates_spec : IsOrbitCoordinates orbitCoordinates :=
  Coordinates.isOrbitCoordinates

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitGeometry

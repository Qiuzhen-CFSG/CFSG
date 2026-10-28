module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.Orbit
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitBound.Transport
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitBound.Refinement
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitBound.Coordinates
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitBound.GraphBound

/-!
# The finite linear-stabilizer bound for the canonical homology orbit

`OrbitBound.Coordinates` identifies the literal column quotient ker(a - 1)/im(a - 1)
with twelve binary coordinates and its distinguished local-subgroup orbit with
the 693 vectors in `OrbitBound.Geometry`. Those vectors span, so
`OrbitBound.Transport` gives a faithful action of the entire orbit linear
stabilizer on their sum graph.

`OrbitBound.GraphBound` checks invariant refinements for six point stabilizers,
with successive bounds 693, 2, 30, 4, 8, 2 and a trivial final stabilizer.
Their product bounds the full graph automorphism group by 2661120. Combining
these certificates proves the unconditional linear-stabilizer bound here.

Preservation by the full involution centralizer remains a separate obligation
for the image-bound consumer. Source motivation: GLS3, Table 5.3i, printed p.270;
the concrete certificate data and ATLAS attribution are in `ImageBound/source/README.md`.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation

/-- Transfer a graph bound through an exact homology-orbit coordinate identification. -/
theorem orbitLinearStabilizer_card_le_of_coordinates
    (e : NaturalHomology ≃ₗ[ZMod 2] OrbitGeometry.CoordinateSpace)
    (he : OrbitGeometry.IsOrbitCoordinates e)
    (hg : Nat.card OrbitGeometry.preservingGroup ≤ 2661120) :
    Nat.card orbitLinearStabilizer ≤ 2661120 :=
  (OrbitGeometry.orbitLinearStabilizer_card_le_graph e he).trans hg

/-- The full group of invertible linear maps preserving the distinguished
canonical homology orbit has order at most 2661120. -/
theorem orbitLinearStabilizer_card_le : Nat.card orbitLinearStabilizer ≤ 2661120 :=
  orbitLinearStabilizer_card_le_of_coordinates
    OrbitGeometry.orbitCoordinates OrbitGeometry.orbitCoordinates_spec
    OrbitGeometry.preservingGroup_card_le

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation

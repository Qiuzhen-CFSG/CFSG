module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.Homology
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.Orbit
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitBound
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitInvariance

/-!
# The canonical homology image bound

Every element of the literal involution centralizer preserves the
distinguished orbit: OrbitInvariance identifies it with the intrinsic
contraction-rank-sixteen fibre. Thus the full homology image is a subgroup
of the orbit's linear stabilizer. OrbitBound embeds that stabilizer in the
sum-graph automorphism group and bounds its order by 2661120, giving the
same bound for the full image on ker(a - 1) / im(a - 1).

The conditional reduction is retained as a separate interface. The final
theorem discharges both premises with these certified results for the
actual column quotient.

Source motivation: GLS3, Table 5.3i, printed p.270, and the representation
attribution in TwoCoreCentralizer/source/README.md.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation

/-- Separate the restriction on all centralizer elements from the finite
linear-stabilizer calculation. Both premises must be proved for assembly. -/
theorem homologyAction_image_card_le_of_orbit_stabilizer
    (hpres : ∀ (c : involutionCentralizer) (v : NaturalHomology),
      v ∈ distinguishedOrbit →
        (homologyAction c : Module.End (ZMod 2) NaturalHomology) v ∈ distinguishedOrbit)
    (hcard : Nat.card orbitLinearStabilizer ≤ 2661120) :
    Nat.card homologyAction.range ≤ 2661120 := by
  exact (Subgroup.card_le_of_le (homologyAction_range_le_orbitLinearStabilizer hpres)).trans hcard

/-- The entire literal involution centralizer has homology image of order
at most 2661120 on the natural column quotient ker(a - 1) / im(a - 1). -/
theorem homologyAction_image_card_le : Nat.card homologyAction.range ≤ 2661120 :=
  homologyAction_image_card_le_of_orbit_stabilizer
    homologyAction_preserves_distinguishedOrbit orbitLinearStabilizer_card_le

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation

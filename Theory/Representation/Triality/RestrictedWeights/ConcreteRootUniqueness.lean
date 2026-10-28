module
public import Theory.Representation.Triality.RestrictedWeights.ConcreteGeometry
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram.Regularity.SpinTangents
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Lifts.RootTransport.RootUniqueness
/-!
# Root-subgroup uniqueness on the pinned Spin carrier

The actual Spin torus and root tangent span is already proved. Apply tangent
rigidity to discharge the uniqueness input used in opposition-prefix transport.
The only retained setup input is algebraic universality of the same carrier.
Source: GLS3 1.9.5(b).
-/

public noncomputable section
open Theory.AlgebraicGroup
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.RestrictedWeights.SteinbergTensors
namespace Triality.RestrictedWeights.Concrete
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu : IsUniversalVersion (groupVariety k))
/-- The concrete Spin tangent span discharges actual root-subgroup uniqueness. -/
theorem rootSubgroupUniqueness : FiniteRestriction.ClassBound.ConnectedCentralizer.Normalizer.RootSubgroupUniqueness
    (finiteGeometry k hu) := by
  apply FiniteRestriction.ClassBound.ConnectedCentralizer.Normalizer.rootSubgroupUniqueness_of_tangent_span
  change LinearMap.range (Bor1.identityTangentMorphismLinearMap (CorootTorus.closedSubgroup k).inclusion) ⊔
    (⨆ a : ULift RootIndex, LinearMap.range
      (Bor1.identityTangentMorphismLinearMap (rootClosedSubgroup k a.down).inclusion)) = ⊤
  simpa only [iSup_ulift] using torus_root_tangent_span k
end Triality.RestrictedWeights.Concrete

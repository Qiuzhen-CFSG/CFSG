module
public import Theory.Representation.Triality.RestrictedWeights.ConcreteRootRecovery.FiniteCharts
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.RootRecovery.LeftReduction
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.RootRecovery.SL2Separation
/-!
# Actual finite triality highest-weight recovery

The central and three-arm SL2 charts map their actual finite subfields into
the prescribed graph-field elementary subgroup. Applying finite SL2 recovery
to those two charts determines all four restricted highest-weight coordinates.
Only the original universality of the supplied algebraic Spin group remains;
there is no chart, finite module, or representation-classification premise.
Source: GLS3 2.8.2 and Steinberg 13.3(a), including n = 1.
-/
public noncomputable section
open Theory.AlgebraicGroup
open Triality.SimplyConnected
open Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
namespace Triality.RestrictedWeights.Concrete
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

theorem leftHighestVectorWeightRecovery (hu : IsUniversalVersion (groupVariety k))
    (n : ℕ) (hn : 0<n) : LeftHighestVectorWeightRecovery (finiteGeometry k hu) n :=
  RootRecovery.leftHighestVectorWeightRecovery_of_finiteRootCharts (finiteGeometry k hu) n
    (RootCharts.finiteRootCharts k hu n hn) RootRecovery.finiteSL2HighestVectorRecovery
end Triality.RestrictedWeights.Concrete

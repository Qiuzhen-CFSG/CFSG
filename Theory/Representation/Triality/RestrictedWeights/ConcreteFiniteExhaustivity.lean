module

public import Theory.Representation.Triality.RestrictedWeights.ConcreteFiniteIrreducibility
public import Theory.Representation.Triality.RestrictedWeights.ConcreteTorusGeometry.FixedFusion
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts.Exhaustivity

/-!
# Finite triality exhaustion from actual highest-vector recovery

The actual restricted modules are irreducible, and their number equals the
proved odd-class upper bound. Exact recovery of a highest weight from the
finite root charts separates them, so they exhaust finite irreducibles.
The sole remaining representation input is the explicitly named root-chart
recovery theorem, owned by the concrete finite-SL₂ construction.
Source: Steinberg 13.3(b), GLS3 2.8.2.
-/

public noncomputable section
open Theory.AlgebraicGroup
open Triality.SimplyConnected
open Triality.RestrictedWeights.SteinbergTensors FiniteRestriction
namespace Triality.RestrictedWeights.Concrete
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu : IsUniversalVersion (groupVariety k))

/-- The literal class-bound consumer; no class count or irreducibility is assumed. -/
theorem leftRestrictedExhaustivity_of_weightRecovery (n : ℕ) (hn : 0 < n)
    (hrec : LeftHighestVectorWeightRecovery (finiteGeometry k hu) n) :
    LeftRestrictedExhaustivity (finiteGeometry k hu) n :=
  leftRestrictedExhaustivity_of_existence_of_classBound _ n hn
    (leftRestrictedIrreducibility k hu n hn)
    (leftRestrictedSeparation_of_finiteHighestLine_of_weightRecovery _ n
      (leftFiniteHighestLine k hu n hn) hrec)
    (restrictedRationalExistence k hu n) (TorusGeometrySource.elementaryClassBound k hu n hn)

end Triality.RestrictedWeights.Concrete

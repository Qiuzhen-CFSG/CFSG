module

public import Theory.Representation.Triality.RestrictedWeights.ConcreteFiniteExhaustivity
public import Theory.Representation.Triality.RestrictedWeights.ConcreteRootRecovery
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts.HighestWeight

/-!
# The actual finite restricted-weight classification for triality

Finite highest lines and the exact central/arm SL₂ charts recover every
restricted highest weight. The q⁴ odd-class bound then shows that the actual
restricted rational modules exhaust finite irreducibles. This discharges all
three finite restriction obligations on the original Spin fixed-point carrier,
including n=1. The only earlier input is algebraic universality of that carrier.
The rational tensor realization is assembled separately from its Chevalley
pinning and the proved rational Steinberg theorem.
Source: Steinberg 13.3; GLS3 Theorem 2.8.2.
-/

public noncomputable section
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
open Triality.SimplyConnected
open Triality.RestrictedWeights.SteinbergTensors FiniteRestriction
namespace Triality.RestrictedWeights.Concrete
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu : IsUniversalVersion (groupVariety k))

theorem leftRestrictedSeparation (n : ℕ) (hn : 0 < n) :
    LeftRestrictedSeparation (finiteGeometry k hu) n :=
  leftRestrictedSeparation_of_finiteHighestLine_of_weightRecovery _ n
    (leftFiniteHighestLine k hu n hn) (leftHighestVectorWeightRecovery k hu n hn)

theorem leftRestrictedExhaustivity (n : ℕ) (hn : 0 < n) :
    LeftRestrictedExhaustivity (finiteGeometry k hu) n :=
  leftRestrictedExhaustivity_of_weightRecovery k hu n hn
    (leftHighestVectorWeightRecovery k hu n hn)

/-- Irreducibility, exact parameter separation and an actual rational lift. -/
theorem finiteRestrictedClassification (n : ℕ) (hn : 0 < n) :
    LeftRestrictedIrreducibility (finiteGeometry k hu) n ∧
      LeftRestrictedSeparation (finiteGeometry k hu) n ∧
      LeftRestrictedExhaustivity (finiteGeometry k hu) n :=
  ⟨leftRestrictedIrreducibility k hu n hn, leftRestrictedSeparation k hu n hn,
    leftRestrictedExhaustivity k hu n hn⟩

/-- Finite intertwiners identify precisely equal restricted highest weights. -/
theorem restriction_equivalent_iff (n : ℕ) (hn : 0 < n)
    (A C : RationalFactor (groupVariety k)) {a b : Weight}
    (ha : InRestrictedRange n a) (hb : InRestrictedRange n b)
    (hA : HasLeftHighestWeight (finiteGeometry k hu) A a)
    (hC : HasLeftHighestWeight (finiteGeometry k hu) C b) :
    Nonempty (Representation.Equiv (A.restrict ((finiteGeometry k hu).inclusion n)).ρ
      (C.restrict ((finiteGeometry k hu).inclusion n)).ρ) ↔ a=b :=
  ⟨leftRestrictedSeparation k hu n hn A C a b ha hb hA hC,
    fun h => restriction_equivalent_of_leftHighestWeight_eq _ A C hA hC h n⟩

end Triality.RestrictedWeights.Concrete

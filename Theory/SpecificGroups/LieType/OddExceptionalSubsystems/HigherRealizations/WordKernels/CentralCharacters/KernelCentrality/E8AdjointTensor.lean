module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.Transport
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E8AdjointTensor.SimpleCommutators
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E8AdjointTensor.OppositionTransfer
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.AdjointBlocks.DividedPowers

/-!
# Assembly of the relative E8 tensor from integral infinitesimal identities

The tensor and its signed simple pinning are fixed in `Candidate`. The source
cubic coefficient vanishes because its inclusion in E8 intertwines divided
powers and the E8 coefficient vanishes. Integral cancellation then proves every
polynomial covariance coefficient from the first-operator commutators, with
no restriction on the eventual coefficient characteristic.

The two constructors below are conditional: the remaining mathematical inputs
are the actual positive commutators and signed opposition of this fixed tensor.
They are not an unconditional construction of `IntegralAdjointData e8Family`.
This module retains that final assembly; the parent's
`e8Six_kernel_central_of_integralAdjointData` consumes the completed data.

Source: GLS3 §§1.10–1.12 and 2.6.2 (`refs/KGroup/GLS3/chapter2.tex`),
the common integral lattice argument for closed root subsystems.
-/

@[expose] public section
noncomputable section
open Matrix Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
attribute [local instance] Classical.decEq
local instance truncationRootFintype : Fintype typeE8Roots := Fintype.ofFinite _

/-- The E6 source truncates quadratically on its literal integral sublattice in E8. -/
lemma source_cubic_zero (a : Bool × Fin 6) : sourceFamily.dividedPower a 3 = 0 := by
  have hi : e8Family.dividedPower a 3 * AdjointBlocks.e8Lattice =
      AdjointBlocks.e8Lattice * sourceFamily.dividedPower a 3 := by
    rcases a with ⟨s, i⟩
    cases s
    · simpa only [e8Family, sourceFamily, numberedFamily, simpleFamily,
        AdjointBlocks.e8Embedding_base_numbered] using
        AdjointBlocks.e8Embedding.fDividedPower_intertwines (simpleIndex i) 3
    · simpa only [e8Family, sourceFamily, numberedFamily, simpleFamily,
        AdjointBlocks.e8Embedding_base_numbered] using
        AdjointBlocks.e8Embedding.eDividedPower_intertwines (simpleIndex i) 3
  have h : AdjointBlocks.e8Lattice * sourceFamily.dividedPower a 3 = 0 := by
    rw [← hi, e8_cubic_zero, Matrix.zero_mul]
  ext i j
  have hij := congrFun (congrFun h (AdjointBlocks.e8Embedding.indexMap i)) j
  simpa only [Matrix.mul_apply, AdjointBlocks.e8Lattice, AdjointBlocks.inclusion,
    AdjointBlocks.e8Embedding.indexMap.injective.eq_iff, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.zero_apply] using hij

end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor

namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality
open Matrix Theory.AlgebraicGroup.StandardRootSystem RootPairing.SimpleGeckGroup
open RootPairing.IntegralGeckConstruction
attribute [local instance] Classical.decEq
local instance tensorAssemblyRootFintype : Fintype typeE8Roots := Fintype.ofFinite _

/-- The complete polynomial tensor construction, conditional only on the
positive and negative integral first-operator calculations. -/
def e8IntegralAdjointData_of_commutators
    (hE : E8AdjointTensor.PositiveCommutators) (hF : E8AdjointTensor.NegativeCommutators) :
    IntegralAdjointData e8Family where
  tensor := E8AdjointTensor.tensor
  covariance a j := by
    apply E8AdjointTensor.covariance_of_integral_commutator sourceFamily e8Family
      E8AdjointTensor.tensor a (E8AdjointTensor.source_cubic_zero a) (e8_cubic_zero a)
    intro k
    rcases a with ⟨s, i⟩
    cases s
    · simpa only [sourceFamily, e8Family, numberedFamily, simpleFamily, fDividedPower_one,
        E8AdjointTensor.adjointMap_apply, Matrix.mulVec_single_one, Matrix.col_apply,
        AdjointBlocks.baseE8_numbered] using hF (simpleIndex i) k
    · simpa only [sourceFamily, e8Family, numberedFamily, simpleFamily, eDividedPower_one,
        E8AdjointTensor.adjointMap_apply, Matrix.mulVec_single_one, Matrix.col_apply,
        AdjointBlocks.baseE8_numbered] using hE (simpleIndex i) k
  pinning := E8AdjointTensor.pinning

/-- The two independent local inputs suffice: all higher coefficients and
pinning are discharged here, and opposition supplies the negative commutators. -/
def e8IntegralAdjointData_of_positive_and_opposition
    (hE : E8AdjointTensor.PositiveCommutators)
    (hO : E8AdjointTensor.IntegralOppositionCovariance) : IntegralAdjointData e8Family :=
  e8IntegralAdjointData_of_commutators hE
    (E8AdjointTensor.negativeCommutators_of_positive_and_opposition hE hO)

end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality

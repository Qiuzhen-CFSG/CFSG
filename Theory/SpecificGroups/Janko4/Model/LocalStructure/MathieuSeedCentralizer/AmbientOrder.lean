module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedAction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.AmbientOrder.IntrinsicBound

/-!
# The order bound for the full ambient seed centralizer

The full centralizer of the literal max1 seed acts on the intrinsic
ten-operator space. The calibrated quartic bounds its image by 887040;
the concrete algebra and exterior constraints embed its kernel in the
known local kernel of order 2048. The kernel-image formula therefore
gives the unconditional ambient upper bound 1816657920.

The original conditional fixed-space route is retained separately. Its
numerical premises are not needed by the intrinsic-action proof.

Source motivation: GLS3, Table 5.3i, printed p.270, and the literal ATLAS
max1 word documented in `Cardinality.Subgroup`. No table identification is
used as a premise.
-/

public section

namespace Janko4.LocalStructure.MathieuSeedCentralizer

/-- Assemble the actual ambient bound once both full-action bounds are proved.
These premises concern the entire ambient centralizer, including actors whose
membership in max1 has not been established. -/
theorem ambientSeedCentralizer_card_le_of_fixedAction_bounds
    (hkernel : Nat.card AmbientOrder.fixedAction.ker ≤ 2)
    (himage : Nat.card AmbientOrder.fixedAction.range ≤ 908328960) :
    Nat.card (ambientSeedCentralizer matrixA_mul_self matrixB_pow_four) ≤ 1816657920 := by
  rw [AmbientOrder.card_centralizer_eq_kernel_mul_image]
  exact Nat.mul_le_mul hkernel himage

/-- The full centralizer in the literal matrix model has at most 1816657920
elements. All intrinsic-action, coordinate, image and kernel premises are proved. -/
theorem ambientSeedCentralizer_card_le :
    Nat.card (ambientSeedCentralizer matrixA_mul_self matrixB_pow_four) ≤ 1816657920 := by
  change Nat.card IntrinsicAlgebra.centralizer ≤ _
  rw [AmbientOrder.card_centralizer_eq_quartic_kernel_mul_image]
  exact Nat.mul_le_mul AmbientOrder.quarticAction_ker_card_le
    AmbientOrder.quarticAction_range_card_le

end Janko4.LocalStructure.MathieuSeedCentralizer

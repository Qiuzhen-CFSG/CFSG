module

public import Theory.Representation.BinaryPermutation.SixCoreExtension.Residual.TwoCore
public import Theory.Representation.BinaryPermutation.SixCoreExtension.Residual.Transport

/-!
# Applying the complementary two-core calculation to unique squares

The intrinsic W:A₄ calculation discharges the two-core premise of the
six-letter unique-square theorem. The independent identification of W:A₄
with the actual centralizer two-residual remains explicit for its assembly
owner to prove.

Source: Aschbacher–Smith, I.2.2(6b), printed pp.410 and 412, combined
manuscript of 1 March 2004.
-/

public section

open Theory.GroupTheory
namespace BinaryPermutation.SixCoreExtension

/-- The residual identity alone now identifies the literal embedded residual core. -/
theorem residualCore_pair_of_residual_identity
    (hres : centralizerTwoResidual (vector (Multiplicative.ofAdd pair)) = pairResidual) :
    centralizerResidualCore (vector (Multiplicative.ofAdd pair)) = pairCore :=
  residualCore_pair_of_identities hres pairResidual_pCoreIn

/-- The W:A₄ two-core premise of the all-vector unique-square consumer is discharged. -/
theorem unique_square_of_residual_identity
    (hres : centralizerTwoResidual (vector (Multiplicative.ofAdd pair)) = pairResidual)
    (v : V) (hv : coreToNatural (Fin 6) v ≠ 0) :
    ∃! w : Model, (vector (Multiplicative.ofAdd v))⁻¹ * w ∈ centralLine ∧
      ∃ x ∈ centralizerResidualCore (vector (Multiplicative.ofAdd v)), x ^ 2 = w :=
  unique_square_of_identities hres pairResidual_pCoreIn v hv

end BinaryPermutation.SixCoreExtension

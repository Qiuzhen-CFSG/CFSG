module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorB.Interpretation
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorB.Numeric

/-!
# The second generator on the literal degree-518 HS tensor section

The 21 kernel rows are invariant under the actual `20 ⊗ 56` second generator.
On the 518 lifted rows its action is the literal published degree-518 second
matrix, modulo the supplied kernel corrections. Packed arithmetic is checked
by the kernel and interpreted as the actual Kronecker matrix with degree-56
coordinates fastest. Neither identity assumes a marked input action.

The final theorem applies both identities to `markedAction_of_certificates`.
The independent first-generator and pivot-inverse premises remain with the
Tensor518 assembly owner; they are not asserted by this module.

Source: R. A. Wilson et al., ATLAS HSG1-f2r20B0, HSG1-f2r56B0 and
HSG1-f2r518B0, and `Binary/source/section518.json`. Attribution and retained
rights are documented in `Binary/source/README.md`; original code is Apache-2.0.
-/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518
open Sporadic.LeechRelated.HS

/-- Invariance of the literal 21-dimensional kernel under the second generator. -/
theorem kernel_b : kernelMatrix * ambientB = bKernelMatrix * kernelMatrix :=
  funext fun i => GeneratorB.kernel_row i (GeneratorB.kernel_checked i)

/-- The second generator induces the published degree-518 matrix on the section,
with precisely the supplied kernel correction in the lifted coordinates. -/
theorem lift_b :
    liftMatrix * ambientB = bCorrectionMatrix * kernelMatrix + targetB * liftMatrix :=
  funext fun i => GeneratorB.lift_row i (GeneratorB.lift_checked i)

/-- Application to the actual marked-action consumer, discharging both of its
B-generator assumptions. The A-generator and pivot premises are independent. -/
theorem markedAction_of_a_pivot_certificates
    (h20 : Nonempty Twenty.MarkedComparison) (C56 : MarkedAction 0)
    (hNa : kernelMatrix * ambientA = aKernelMatrix * kernelMatrix)
    (hUa : liftMatrix * ambientA = aCorrectionMatrix * kernelMatrix + targetA * liftMatrix)
    (hR : pivotMinor * pivotInverse = 1) : Nonempty (MarkedAction 2) :=
  markedAction_of_certificates h20 C56 hNa kernel_b hUa lift_b hR

end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518

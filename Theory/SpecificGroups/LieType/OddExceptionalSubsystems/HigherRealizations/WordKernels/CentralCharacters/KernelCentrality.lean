module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.Transport

/-!
# Centrality of relative E6 matrix kernels from the integral adjoint tensors

The two applications below use the literal `sourceSix`, `e7Six` and `e8Six`
evaluations. Generator covariance for an integral tensor gives commutation
with its image; the pinned simple operators and the proved quadratic
truncation then give centrality within the six-node image. No assertion of
centrality in the entire E7 or E8 cover is made.

The integral tensor construction is still an explicit premise. These
conditional applications do not complete the unconditional relative-kernel
centrality theorem until both tensors have been constructed. The exact
consumer is `centralCharacterComparison_of_central_kernel`; its independent
center and diagram calculations remain with that consumer's producers.

Source: GLS3 §§1.10–1.12 and 2.6.2, the integral construction of subsystem
representations (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section

namespace TwistedE6.FoldedSubsystem.HigherRealizations
open Theory.AlgebraicGroup.StandardRootSystem RootPairing.SimpleGeckGroup
open KernelCentrality
attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

/-- Application to the actual E7 six-node values. The only undischarged premise
is the finite integral adjoint tensor calculation, independent of the field. -/
theorem e7Six_kernel_central_of_integralAdjointData
    (d : IntegralAdjointData e7Family) (F : Type*) [Field F]
    (hodd : Odd (ringChar F)) (w : SixNodeWord F) (hw : sourceSix F w = 1)
    (z : SixNodeWord F) : Commute (e7Six F w) (e7Six F z) := by
  apply Subtype.ext
  exact d.kernel_central F (two_ne_zero_of_odd F hodd) e7_cubic_zero
    ((splitCarrier F).subtype.comp (sourceSix F))
    ((Subgroup.subtype _).comp (e7Six F))
    (by
      intro s i t
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, sourceSix_of, simpleRoot_val]
      rfl)
    (by
      intro s i t
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, e7Six_of, signedSimple_val]
      rfl)
    w (by simp [hw]) z

/-- The same integral-to-field passage for the actual E8 six-node image.
It does not assert centrality in the entire E8 carrier. -/
theorem e8Six_kernel_central_of_integralAdjointData
    (d : IntegralAdjointData e8Family) (F : Type*) [Field F]
    (hodd : Odd (ringChar F)) (w : SixNodeWord F) (hw : sourceSix F w = 1)
    (z : SixNodeWord F) : Commute (e8Six F w) (e8Six F z) := by
  apply Subtype.ext
  exact d.kernel_central F (two_ne_zero_of_odd F hodd) e8_cubic_zero
    ((splitCarrier F).subtype.comp (sourceSix F))
    ((Subgroup.subtype _).comp (e8Six F))
    (by
      intro s i t
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, sourceSix_of, simpleRoot_val]
      rfl)
    (by
      intro s i t
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, e8Six_of, signedSimple_val]
      rfl)
    w (by simp [hw]) z

end TwistedE6.FoldedSubsystem.HigherRealizations

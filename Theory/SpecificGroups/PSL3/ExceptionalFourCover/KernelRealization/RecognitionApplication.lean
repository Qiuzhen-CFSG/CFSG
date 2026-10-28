module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.Recognition

/-!
# Applying the exceptional realization to universal-kernel recognition

The constructed finite quasisimple covering and its literal kernel equivalence
discharge the existence input of `kernelEquivOfCoverAndBound`. Only the
independent upper bound on the canonical universal kernel remains explicit.
The source-theorem assembly owns that bound and the final field transport.

Source: Aschbacher–Smith I.1.3(6), printed p.407; GLS3 §6.1, Theorem 6.1.4.
-/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.KernelModel

/-- The concrete exceptional cover discharges the realization premise of recognition. -/
noncomputable def universalKernelEquivOfBound
    (hbound : Nat.card cover.toMonoidHom.ker ≤ 48) :
    cover.toMonoidHom.ker ≃* Multiplier :=
  kernelEquivOfCoverAndBound realization realizationKernelEquiv hbound

end Matrix.PSL3.ExceptionalFourCover.KernelModel

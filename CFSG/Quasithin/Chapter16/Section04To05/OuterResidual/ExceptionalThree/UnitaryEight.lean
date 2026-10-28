module

public import Theory.SpecificGroups.SU3.UnitaryEight.Reduction

/-!
# The intrinsic PSU₃(8) calculation in the exceptional cubic branch

The imported reductions retain the actual Hermitian unitary matrices,
PSU image in the projective scalar quotient, and compatible conjugation.
They exclude the Hermitian field-involution case and reduce oddness of the
full automorphism centralizer to the linear projective matrix calculation,
semilinear coverage, and faithfulness of the field component.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of 16.4.8,
printed p.1188. These three premises remain to be discharged; the unconditional
intrinsic result is not yet asserted. Final assembly stays in this module.
The ambient three-prime-kernel projection and the nonsplit U₃-circle(8)
alternative belong to the exceptional-branch owner.
-/

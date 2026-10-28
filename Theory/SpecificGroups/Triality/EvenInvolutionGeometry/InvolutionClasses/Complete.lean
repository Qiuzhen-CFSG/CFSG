module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ArmsReduction
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ShortApplication
public import Theory.SpecificGroups.Triality.ParabolicGeometry
/-!
# The complete two-root-class theorem for binary triality

The genuine unipotent Sylow theorem, the arms-radical normalization, and the
central short-leading calculation discharge all inputs in the original
involution reduction. No Sylow witness or conjugacy-class premise remains.
The result includes the field of two elements.

Source: Aschbacher–Smith 16.1.4(1), printed p.1171.
-/

public section
namespace Triality.Standard.EvenInvolutionGeometry
open Parabolics
/-- The two actual root classes exhaust all involutions in binary triality,
including the field with two elements. -/
theorem involution_isLongRoot_or_isShortRoot (n : ℕ) (hn : 0<n)
    (r : BinaryCarrier n hn) (hr : orderOf r=2) :
    IsLongRootInvolution n hn r ∨ IsShortRootInvolution n hn r :=
  involution_isLongRoot_or_isShortRoot_of_arms_reduction n hn
    (unipotentSylow (binaryParameters n hn) rfl) (coe_unipotentSylow _ _)
    (ArmsNormalization.arms_reduction (binaryParameters n hn) rfl) r hr
end Triality.Standard.EvenInvolutionGeometry

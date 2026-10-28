module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.ShortLeading

/-!
# Removing the short-leading premise from triality involution classification

The genuine conjugacy calculation supplies the literal central-radical
short-root input in the existing two-class reduction. The remaining premise
concerns only involutions in the independent arms radical, with the original
Sylow witness and actual carrier conjugacies retained.

Source: Aschbacher–Smith 16.1.4(1), printed p.1171.
-/

public section
namespace Triality.Standard.EvenInvolutionGeometry
open Parabolics RadicalCoordinates.Centers Parabolics.CentralRootSquare

/-- The proved short-leading calculation leaves only the independent arms reduction. -/
theorem involution_isLongRoot_or_isShortRoot_of_arms_reduction
    (n : ℕ) (hn : 0 < n)
    (S0 : Sylow 2 (BinaryCarrier n hn))
    (hS0 : (S0 : Subgroup _) = unipotent (binaryParameters n hn))
    (harms : ∀ u : radical (binaryParameters n hn) .arms, orderOf u.val = 2 →
      (∃ z : highestRoot (binaryParameters n hn), IsConj u.val z.val) ∨
      (∃ v : radical (binaryParameters n hn) .central,
        (firstLayer (binaryParameters n hn) rfl v).1 ≠ 0 ∧ IsConj u.val v.val))
    (r : BinaryCarrier n hn) (hr : orderOf r = 2) :
    IsLongRootInvolution n hn r ∨ IsShortRootInvolution n hn r :=
  involution_isLongRoot_or_isShortRoot_of_radical_reductions n hn S0 hS0
    (ShortNormalization.isShortRoot_of_first_ne_zero n hn) harms r hr
end Triality.Standard.EvenInvolutionGeometry

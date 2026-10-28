module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.InvolutionFibers.Data

/-!
# Sizes of the finite affine square-one solution sets

These are counts of eleven-bit masks in the actual certified kernel basis.
The first class's solutions with witness index zero fuse to `a`; removing
those leaves 32 masks. The second fiber has 128 square-one masks in total.
These finite counts do not by themselves identify either set with a group
fiber: that requires the square equation, normal form and fusion arguments.

Source: the ATLAS J4G1-max1W1 words and the affine certificates documented
in `Max1Fusion.InvolutionFibers.Data`. All counts below use kernel reduction.
-/

@[expose] public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound
open Cardinality.QuotientCount.Image Simplicity.Max1Fusion.InvolutionFibers

/-- Solutions of the square-one equation for the specified quotient lift. -/
def affineSolutions (b : Bool) : Finset (Fin 2048) :=
  Finset.univ.filter (fun m =>
    Nat.xor (maskImage (actionMasks b) m.val) m.val = squareMask b)

/-- Exclude the first representative, which is conjugate to `a` in Model. -/
def nonFirstSolutions : Finset (Fin 2048) :=
  (affineSolutions false).filter (fun m => (witness false m.val).1 ≠ 0)

set_option maxRecDepth 10000 in
 theorem affineSolutions_false_card : (affineSolutions false).card = 64 := by
  decide +kernel

set_option maxRecDepth 10000 in
 theorem affineSolutions_true_card : (affineSolutions true).card = 128 := by
  decide +kernel

set_option maxRecDepth 10000 in
 theorem nonFirstSolutions_card : nonFirstSolutions.card = 32 := by
  decide +kernel

end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound

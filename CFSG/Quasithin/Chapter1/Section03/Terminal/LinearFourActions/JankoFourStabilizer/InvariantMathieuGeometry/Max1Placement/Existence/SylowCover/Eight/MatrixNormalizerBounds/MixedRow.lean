module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.FirstPureOvergroup.WordComparison
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.ThirdConjugacy.PCComparison

/-!
# Full ambient normalizer control for the mixed Sylow eight

The two pure-row comparisons already identify g18 with kernel mask 1011
and g17*g18 with mask 571. The checked XOR law and cancellation therefore
identify g17 with mask 456. Together with the existing comparisons for g19
and g20, this discharges the mixed row's three word premises. Its full
ambient normalizer lies strictly inside the proper literal max1 subgroup.

Source context: the sporadic Sylow-overgroup analysis cited in
Aschbacher–Smith A.3.12, printed pp.47–48, and Kleidman–Wilson (1988),
pp.484–510. The imported comparisons retain the original ATLAS matrices,
literal word conventions and kernel coordinates. No catalogue or
presentation premise is used.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open Janko4 Janko4.LocalStructure.SylowNormalEights.MatrixWords
attribute [local irreducible] modelGroup matrixA matrixB kernelMask pcGenerator

/-- The mixed generator is recovered from the two certified pure-row comparisons. -/
theorem pcGenerator17_eq_kernelMask : (pcGenerator 17 : Model) = kernelMask 456 := by
  apply mul_right_cancel (b := (pcGenerator 18 : Model))
  exact ThirdConjugacy.pc_pair_eq_kernelMask.trans
    ((ThirdConjugacy.kernelMask_xor 456 1011).trans
      (congrArg (kernelMask 456 * ·) pcGenerator18_eq_kernelMask.symm))

/-- The full ambient normalizer of the mixed row lies strictly in proper max1. -/
theorem row_one : EightNormalizerAlternative (U 1) :=
  row_one_of_word_equalities pcGenerator17_eq_kernelMask
    pcGenerator19_eq_kernelMask pcGenerator20_eq_kernelMask

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds

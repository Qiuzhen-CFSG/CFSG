module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Blocks
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsTwentyToTwentySix.Twenty
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsTwentyToTwentySix.TwentyOne
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsTwentyToTwentySix.TwentyTwo
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsTwentyToTwentySix.TwentyThree
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsTwentyToTwentySix.TwentyFour
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsTwentyToTwentySix.TwentyFive

/-!
# Literal J₂ word-column checks for catalogue indices 20–25

The six finite certificates check the unchanged candidate columns against the
literal reverse-norm sums. Their shorter inverse walks are proved equal to the
original walks using exhaustive raw-table identities. No subgroup-cache
correctness or group-geometric premise is used.

This discharges the fourth word-range premise of
Coefficients.columnChecks_of_word_ranges. The other word ranges and the
independent row comparison remain with that theorem's assembly owner.
Source and original ATLAS attribution: Columns/source/README.md.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns

/-- Every literal word column in the final six-entry catalogue range. -/
theorem wordChecks_twentyToTwentySix : WordChecksIn 20 26 := by
  intro d h20 h26
  have hd : d = 20 ∨ d = 21 ∨ d = 22 ∨ d = 23 ∨ d = 24 ∨ d = 25 := by
    simp only [Fin.ext_iff]
    change d.val = 20 ∨ d.val = 21 ∨ d.val = 22 ∨ d.val = 23 ∨ d.val = 24 ∨ d.val = 25
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact WordsTwentyToTwentySix.wordChecks20
  · exact WordsTwentyToTwentySix.wordChecks21
  · exact WordsTwentyToTwentySix.wordChecks22
  · exact WordsTwentyToTwentySix.wordChecks23
  · exact WordsTwentyToTwentySix.wordChecks24
  · exact WordsTwentyToTwentySix.wordChecks25

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns

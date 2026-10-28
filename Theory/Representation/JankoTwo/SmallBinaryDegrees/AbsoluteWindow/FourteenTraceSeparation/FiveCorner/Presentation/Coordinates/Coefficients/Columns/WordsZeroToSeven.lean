module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Blocks
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsZeroToSeven.WordZero
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsZeroToSeven.WordOne
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsZeroToSeven.WordTwo
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsZeroToSeven.WordThree
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsZeroToSeven.WordFour
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsZeroToSeven.WordFive
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsZeroToSeven.WordSix

/-!
# Exact literal word columns for catalogue entries 0 through 6

Each of the seven word modules certifies all 126 blocks of eight original
roots. The packed evaluator is proved equal to the fixed original actions,
with the literal inverse words and all 25 power pairs retained. The theorem
below discharges the first premise of columnChecks_of_word_ranges.

Source: Columns/source/README.md and the unchanged Columns/Catalogue.lean.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns

/-- Unconditional arithmetic certificate for the first seven catalogue words. -/
theorem wordChecks_zeroToSeven : WordChecksIn 0 7 := by
  intro d _ hd
  have h : d.val = 0 ∨ d.val = 1 ∨ d.val = 2 ∨ d.val = 3 ∨
      d.val = 4 ∨ d.val = 5 ∨ d.val = 6 := by omega
  rcases h with h | h | h | h | h | h | h
  · have e : d = (0 : Fin 26) := by
      apply Fin.ext
      exact h
    exact e.symm ▸ WordsZeroToSeven.wordChecks_zero
  · have e : d = (1 : Fin 26) := by
      apply Fin.ext
      exact h
    exact e.symm ▸ WordsZeroToSeven.wordChecks_one
  · have e : d = (2 : Fin 26) := by
      apply Fin.ext
      exact h
    exact e.symm ▸ WordsZeroToSeven.wordChecks_two
  · have e : d = (3 : Fin 26) := by
      apply Fin.ext
      exact h
    exact e.symm ▸ WordsZeroToSeven.wordChecks_three
  · have e : d = (4 : Fin 26) := by
      apply Fin.ext
      exact h
    exact e.symm ▸ WordsZeroToSeven.wordChecks_four
  · have e : d = (5 : Fin 26) := by
      apply Fin.ext
      exact h
    exact e.symm ▸ WordsZeroToSeven.wordChecks_five
  · have e : d = (6 : Fin 26) := by
      apply Fin.ext
      exact h
    exact e.symm ▸ WordsZeroToSeven.wordChecks_six

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns

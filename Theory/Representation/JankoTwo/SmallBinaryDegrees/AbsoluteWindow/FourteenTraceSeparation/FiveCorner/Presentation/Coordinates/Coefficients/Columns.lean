module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Model
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Arithmetic
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Blocks

/-!
# Shared finite checks for the nine reverse-norm columns

`Columns.Catalogue` checks that the 26 literal words recover all 65 occurrences
in the original nine generators. `Columns.Data` contains candidate packed word
columns. `columnChecks_of_word_ranges` combines four complete word families
and the independent original-row comparison into the exact `ColumnChecks`.

The numerical premises remain explicit until their producers have proved them.
No correctness of the subgroup-action cache or group geometry is assumed here.

Source: Columns/source/README.md and Coefficients/source/README.md.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients

/-- Assemble the literal column comparisons, discharging both numerical layers. -/
theorem columnChecks_of_word_ranges
    (h₀ : Columns.WordChecksIn 0 7) (h₁ : Columns.WordChecksIn 7 14)
    (h₂ : Columns.WordChecksIn 14 20) (h₃ : Columns.WordChecksIn 20 26)
    (hrows : Columns.RowChecks) : ColumnChecks :=
  columnChecks_of_shared_words (Columns.wordChecks_of_ranges h₀ h₁ h₂ h₃) hrows

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients

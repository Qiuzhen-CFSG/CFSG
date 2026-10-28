module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Blocks
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Rows.Checks

/-!
# All original row comparisons for the nine generator columns

The candidate XORs are compared in bounded kernel certificates with packed
copies of the unchanged row arrays. The proved packing identity recovers the
literal `columnFromRows` traversal for every original output index. This
supplies the independent row premise of `columnChecks_of_word_ranges`.

Source: Columns/source/README.md and Rows/source/README.md.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns

/-- Every candidate generator column equals its column in the original rows. -/
theorem rowChecks : RowChecks := by
  intro k j
  exact (Rows.combined_eq_fastColumn k j).trans (Rows.fastColumn_eq k j)

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns

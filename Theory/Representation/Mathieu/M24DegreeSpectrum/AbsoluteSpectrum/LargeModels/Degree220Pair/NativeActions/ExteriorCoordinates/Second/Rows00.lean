module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second.Masks

/-!
# Second-generator compound rows 0 through 41

The packed determinant evaluates all 462 column five-subsets together.
This bounded batch is checked by Lean's kernel against the saved exterior rows.
See `source/README.md` for the arithmetic proof and measurements.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second

/-- Exact packed determinant identities for the indicated 42 native rows. -/
theorem rows00 : ∀ i : Fin 42,
    packedRow (rowIndex 0 i) = exteriorRowsB[(rowIndex 0 i).val]! := by
  decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second

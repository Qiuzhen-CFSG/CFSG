module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Inverse
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.ColumnChecks.Recursion

/-!
# Checked column orbit and left inverse for the degree-896 HS representation

The saved column vectors are stored as rows. Their 895 recursion equations are
checked against the literal generator transposes and then interpreted as
`Matrix.mulVec` equations. The saved inverse is checked on the left, row by row.
These unconditional certificates discharge exactly the two column premises of
`columnOrbitSpan_eq_top_of_checks` in the parent assembly module.

Source: `Certificates/source/witnesses.json.gz` and its README. See also
`OrbitSpans/source/README.md` and `ColumnChecks/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans

/-- The literal saved column orbit follows the selected generator's column action. -/
theorem column_recursion_checked : ColumnRecursion := ColumnChecks.recursion_checked

/-- The literal saved inverse is a left inverse of the stored column-orbit matrix. -/
theorem column_inverse_checked : columnInverse * columnMatrix = 1 := ColumnChecks.inverse_checked

end Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans

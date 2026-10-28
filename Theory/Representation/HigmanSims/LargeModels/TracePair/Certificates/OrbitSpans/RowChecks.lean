module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.RowChecks.Inverse
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans.RowChecks.Recursion

/-!
# The saved HS row orbit recursion and left inverse

Every saved parent row is multiplied on the right by its selected shared packed
generator. The saved inverse multiplies the orbit matrix on the left. Bounded
kernel checks establish all 895 recursion equations and all 896 inverse rows;
the sound packed-product bridges yield the exact matrix statements below.

Source: `Certificates/source/witnesses.json.gz` and its README.
The application is `rowOrbitSpan_eq_top_of_checks` in `OrbitSpans.lean`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans

/-- The literal saved parent and generator arrays give the right-action recursion. -/
theorem row_recursion_checked : RowRecursion :=
  RowChecks.recursion_of_checkedRange RowChecks.recursion_range_checked

/-- The saved candidate is a left inverse of the matrix of saved orbit rows. -/
theorem row_inverse_checked : rowInverse * rowMatrix = 1 :=
  RowChecks.inverse_of_checkedRange RowChecks.inverse_range_checked

end Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans

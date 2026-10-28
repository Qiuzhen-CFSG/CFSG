module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag

/-!
# Application of the checked matrices to the native quotient flag

The matrix certificate discharges the inverse, intertwining, upper-block and
diagonal-block assumptions of the actual coset-module flag construction.
The native action-table comparison is independent and remains explicit here.
This application is separate so that the existing flag assembly can import
`MatrixChecks` without an import cycle.

Source: James, J. Algebra 27 (1973), 57–111; witness conventions in
`PointSimpleDegrees/source/README.md`.
-/

public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks

/-- The actual invariant stages and literal quotient coordinates, with all
matrix premises discharged. Native coset-action certification is independent. -/
noncomputable def flagCoordinates_of_native_action
    (h : NativeBridge.NativeAction) : FlagCoordinates :=
  flagCoordinates_of_native_certificates h matrixIdentities

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks

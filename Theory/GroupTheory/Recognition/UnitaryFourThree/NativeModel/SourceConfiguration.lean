module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.NativeModel.IsType
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

/-!
# Literal native source geometry for the U₄(3) comparison

The original type theorem constructs the exact marked cubic geometry on
any Sylow-three subgroup of the native involution centralizer. Its roots,
quaternion factors, kernels and ambient maps are those of the existing
source configuration. This is the model-side input to the abstract graph
and group comparison, with no model geometry field left as an assumption.

Source: Aschbacher, *Sporadic Groups* (1994), §45, printed pp.244–249.
-/

public section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType
open Theory.GroupTheory.Recognition.UnitaryFourThree

/-- The exact native marked configuration used by the two-type comparison. -/
theorem native_source_configuration (P : Sylow 3 standardCentralizer) :
    Nonempty (CubicGeometry.SourceConfiguration native_isType P) :=
  native_isType.original_cubic_source_configuration P

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.SourceType

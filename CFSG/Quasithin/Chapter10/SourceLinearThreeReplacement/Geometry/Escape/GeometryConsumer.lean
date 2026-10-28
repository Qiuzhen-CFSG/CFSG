module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Assembly

/-!
# Applying diagonal escape to the original centralizer geometry

The diagonal-fusion, offender and pair-action arguments discharge the escape
clause for every original central involution.
The fixed-space and two-core inputs retain their existing independent owners.
This application is separate from the escape proof so the geometry owner can
import that proof without a dependency cycle.

Source: Aschbacher--Smith 10.2.11 and 10.3.1--2, printed pp.753--756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Application to the original centralizer-data consumer, preserving its
independently owned fixed-space and two-core premises. -/
theorem centralizerGeometry_of_fixed_core_wholeModuleTI
    (hfixed : FixedSpaceTIAt T) (hcore : CoreReducedAt T)
    (hwhole : WholeModuleTIAt T) : CentralizerGeometryAt T :=
  centralizerGeometry_of_source_inputs hfixed hcore (escape_of_wholeModuleTI hwhole)

/-- The original centralizer-data consumer with its escape clause proved.
Only the independently owned fixed-space and two-core inputs remain. -/
theorem centralizerGeometry_of_fixed_core
    (hfixed : FixedSpaceTIAt T) (hcore : CoreReducedAt T) : CentralizerGeometryAt T :=
  centralizerGeometry_of_source_inputs hfixed hcore (escapeAt T)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape

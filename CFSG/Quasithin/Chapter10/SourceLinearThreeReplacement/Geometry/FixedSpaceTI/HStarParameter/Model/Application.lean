module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.Model.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.Source

/-!
# Applying the wreath calculation to the literal H-star quotient

The constructed faithful subrepresentation discharges the model premise in
the source H-star parameter theorem. The actual quotient geometry and the
earlier Hall-faithfulness input remain explicit, with final discharge owned
by the H-star parameter assembly and its existing source producers.

Source: Aschbacher--Smith 10.3.1, printed pp.755--756.
-/

public section
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The model premise is discharged by the actual faithful wreath submodule. -/
theorem hStarLocalA_of_geometry
    (hhall : SourceNonnormalHallFaithfulAt T) (hgeometry : QuotientGeometryAt T) :
    HStarLocalAAt T :=
  hStarLocalA_of_geometry_and_model hhall hgeometry wreathFixedSeedBound

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter

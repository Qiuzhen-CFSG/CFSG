module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.GlobalParameter.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Source

/-!
# Centralizer geometry after the global parameter calculation

The actual full-automizer involution bound supplies the global parameter
in the source fixed-space contradiction. The proved core/reducedness and
escape arguments then give the original centralizer geometry. The independent
H*-constituent parameter and half-Sylow uniqueness remain explicit here.
Their producers are qt-d-10-fixed-hstar-parameter and
qt-d-10-nona5-half-sylow-unique; final discharge stays with
qt-d-10-replacement-centralizer-geometry and its replacement consumer.

Source: Aschbacher--Smith 10.2.10--11 and 10.3.1--2, printed pp.753--756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The source global parameter has been discharged; only the independent
H* constituent calculation remains in the fixed-space contradiction. -/
theorem fixed_part_of_hStar_parameter
    (ha : FixedSpaceTI.HStarLocalAAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ :=
  FixedSpaceTI.fixed_part_of_parameter_inputs
    (FixedSpaceTI.GlobalParameter.globalSAt T) ha hmany D s

/-- Fixed-space vanishing and TI on the literal full module, retaining precisely
the independently owned local parameter and half-Sylow inputs. -/
theorem fixedSpaceTI_of_local_inputs
    (ha : FixedSpaceTI.HStarLocalAAt T)
    (hhalf : PointControl.HalfSylowUniqueAt T) : FixedSpaceTIAt T :=
  FixedSpaceTI.fixedSpaceTI_of_source_inputs
    (FixedSpaceTI.GlobalParameter.globalSAt T) ha hhalf

/-- Every original centralizer-geometry output follows once the two independent
earlier source inputs are supplied. The core and escape premises are discharged. -/
theorem centralizerGeometry_of_local_inputs
    (ha : FixedSpaceTI.HStarLocalAAt T)
    (hhalf : PointControl.HalfSylowUniqueAt T) : CentralizerGeometryAt T :=
  centralizerGeometry_of_source_inputs (fixedSpaceTI_of_local_inputs ha hhalf)
    (CoreReduced.coreReducedAt T) (Escape.escapeAt T)

/-- Apply the improved geometry to the actual replacement construction.
The final replacement owner discharges its wreath and overgroup arguments. -/
theorem replacement_of_local_geometry_inputs
    (ha : FixedSpaceTI.HStarLocalAAt T)
    (hhalf : PointControl.HalfSylowUniqueAt T)
    (hwreath : WreathRecognitionAt T) (hovergroups : OvergroupSpanAt T) :
    SourceLinearThreeReplacementAt T :=
  replacement_of_source_inputs (centralizerGeometry_of_local_inputs ha hhalf)
    hwreath hovergroups

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry

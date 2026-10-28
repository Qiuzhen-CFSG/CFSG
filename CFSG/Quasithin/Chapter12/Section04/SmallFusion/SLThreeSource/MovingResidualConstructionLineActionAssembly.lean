module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionLineAction
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionInverter

/-!
# Moving-residual consumers with both quotient actions proved

The actual centralizing line has order three, and the original Sylow actor
inverts the other line. Supply both calculations to the moving-residual
contradiction and the literal Chapter 14 fusion input. The separate linear
block marking and earlier source premises remain with the source assembly
owner; no line-action or inverter premise remains here.

Source: Aschbacher–Smith, proof of 12.4.6 and Lemma 12.4.7, printed p.814.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u

/-- The moving-residual consumer with both source quotient actions supplied. -/
theorem movingResidualCalculation_of_block
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (block : MovingLinearBlockCalculation.{u}) : MovingResidualCalculation.{u} :=
  movingResidualCalculation_of_block_and_line structural marked block
    (movingCentralizingLineCalculation structural marked)

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource
open Chapter12.Section02 Chapter12.Section04.SmallFusion
open Chapter12.Section04.SmallFusion.SLThreeSource
universe u

/-- Apply the completed quotient-action calculations to the actual fusion input. -/
theorem slThreeFusion1247_of_moving_line_action
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (localFacts : LocalCalculations.{u}) (fixed : FixedResidualCalculation.{u})
    (block : MovingLinearBlockCalculation.{u}) : SLThreeFusion1247.{u} :=
  slThreeFusion1247_of_calculations structural marked localFacts fixed
    (movingResidualCalculation_of_block structural marked block)

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource

module

public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource.FusionInput
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.Source

/-!
# The completed original L₃ fusion input

The source construction supplies the local geometry and both residual
calculations to the literal `SLThreeFusion1247` adapter. Its only remaining
inputs are the permitted structural and marked-module implications of
Section 12.2. The fixed-space application retains the independent 12.4.1/8/9
commutator branch; the final Section 13.3 assembly discharges that branch
and the earlier Section 12.2 inputs.

This extension sits after the existing conditional fusion adapter, which
is already imported by the residual action producers.
Source: Aschbacher–Smith, 12.4.5–7, pp.813–814, and the proof of 12.4.2, p.816.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource
open Chapter12.Section02 Chapter12.Section04.SmallFusion
open Chapter12.Section04.SmallFusion.SLThreeSource
universe u

/-- The exact original fusion contract with every local 12.4.5–6 premise
discharged; only the earlier Section 12.2 source implications remain. -/
theorem slThreeFusion1247_of_source
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple) :
    SLThreeFusion1247.{u} :=
  slThreeFusion1247_of_calculations structural marked
    (localCalculations_of_source structural marked)
    (fixedResidualCalculation_of_source structural marked)
    (movingResidualCalculation_of_source structural marked)

/-- Apply the completed fusion branch to the original fixed-space consumer.
The independent symmetric-commutator branch retains its own source contract. -/
theorem slThreeFixedSpace1242_of_source_fusion
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (geometry : SLThreeCommutator1242.{u}) : SLThreeFixedSpace1242.{u} :=
  slThreeFixedSpace1242_of_fusion_and_commutator
    (slThreeFusion1247_of_source structural marked) geometry

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource

module

public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource.FixedSpace
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.Assembly

/-!
# The original L₃(2) fusion input for the D fixed-space contradiction

This adapter applies the Sylow-centralizer construction to the literal
SLThreeFusion1247 contract and then to the existing fixed-space contradiction.
The structural and marked 12.2 inputs and the three 12.4 local calculations
remain explicit. Final source assembly must discharge each of them.
The moving-residual implication uses the fixed fourth member of the actual
four-subgroup family; no assertion of weak closure in T is used.

Source: Aschbacher–Smith, 12.4.5–7 and the final proof of 12.4.2, pp.813–816.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section03.CaseOneSource
open Chapter12.Section02 Chapter12.Section04.SmallFusion
open Chapter12.Section04.SmallFusion.SLThreeSource
universe u

theorem slThreeFusion1247_of_calculations
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (localFacts : LocalCalculations.{u}) (fixed : FixedResidualCalculation.{u})
    (moving : MovingResidualCalculation.{u}) : SLThreeFusion1247.{u} := by
  intro G _ _ T L V h D hmodel hne
  obtain ⟨z, hz, hgen, hcent, hweak, _⟩ := fusion_of_calculations
    h D structural marked hmodel hne localFacts fixed moving
  exact ⟨z, hz, hgen, hcent, hweak⟩

/-- The actual consumer application; the independent commutator branch is
retained with its source owner. -/
theorem slThreeFixedSpace1242_of_local_sources
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (localFacts : LocalCalculations.{u}) (fixed : FixedResidualCalculation.{u})
    (moving : MovingResidualCalculation.{u}) (geometry : SLThreeCommutator1242.{u}) :
    SLThreeFixedSpace1242.{u} :=
  slThreeFixedSpace1242_of_fusion_and_commutator
    (slThreeFusion1247_of_calculations structural marked localFacts fixed moving) geometry

end CFSG.Quasithin.Chapter14.Section03.CaseOneSource

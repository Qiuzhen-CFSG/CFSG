module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Local.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Generation.Source

/-!
# Completion of the original diagonal seed analysis

The local residual calculation and the natural-module generation calculation
supply all five fields for the same original configuration. No further seed
calculation is assumed. The centralizer two-core assembly consumes this result.

Source: Aschbacher--Smith 10.1.3 and 10.2.11, printed pp.742,753--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed
variable {G : Type*} [Group G] [Finite G]

/-- The complete original seed analysis, including the literal residual action. -/
theorem seedAnalysisAt (T : Sylow 2 G) : SeedAnalysisAt T :=
  seedAnalysisAt_of_calculations (Local.localCalculationAt T) (Generation.moduleGenerationAt T)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed

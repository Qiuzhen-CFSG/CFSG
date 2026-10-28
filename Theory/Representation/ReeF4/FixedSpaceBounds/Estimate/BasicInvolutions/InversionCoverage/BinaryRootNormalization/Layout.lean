module

public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.Layout
-- This internal specification extends the existing index-table specification
-- by identifying its block carrier. No hidden definition is re-exported.
import all Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization.RootAlignment

/-!
# The block carrier underlying the binary normalization

The positive word layout uses the published positive root-block table.
This equation connects its factorization theorems to Parrott's literal
matrix words. The internal import is confined to this specification proof;
consumers use the equation and the existing public index-table equations.

Source: GLS3 Table 2.4, types V and VI; Parrott (1972), §5, p.683.
-/

public section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.Normalization
open Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

theorem positive_layout_blocks : positiveRootWordLayout.blocks = rootBlocks .positive := by
  rfl

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.Normalization

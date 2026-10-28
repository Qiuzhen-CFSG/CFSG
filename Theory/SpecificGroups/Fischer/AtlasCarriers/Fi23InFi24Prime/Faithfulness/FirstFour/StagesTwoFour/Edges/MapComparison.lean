module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.Tables
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Tables
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.MapComparison.Checks
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.MapComparison.Forward
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.Checker

/-!
# Comparison of the signed middle-stage tables with the literal model

The positive actions use the shared staged word certificates and the last-four
agreement. Checked left inverses then give every negative action. The actual
Schreier membership consumer below retains the two independent stage checks.
The remaining finite-certificate premises are explicit; these conditional
results do not yet assert `cachedMaps_correct_of_lastFour`.
Source: GLS3 Table 5.3v, ATLAS F24G1-p306936B0, and the retained word DAG.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.Edges

/-- Full signed comparison from the independently owned staged certificates. -/
theorem cachedMaps_correct_of_checks
    (hs : LastFour.Transitions.Staged.SeedChecks)
    (hm : LastFour.Transitions.Staged.MiddleChecks)
    (hi : MapComparison.InverseChecks)
    (hl : LastFour.Transitions.TableAgreement) : MapsCorrect cachedMaps :=
  MapComparison.mapsCorrect_of_forward_inverse
    (MapComparison.forward_of_stagedChecks hs hm hl) hi

/-- Application to the literal middle Schreier words, preserving both stage obligations. -/
theorem nonTreeEdges_of_mapComparison_checks
    (hs : LastFour.Transitions.Staged.SeedChecks)
    (hm : LastFour.Transitions.Staged.MiddleChecks)
    (hi : MapComparison.InverseChecks)
    (hl : LastFour.Transitions.TableAgreement)
    (h₂ : StageChecks cachedMaps 0) (h₃ : StageChecks cachedMaps 1) : NonTreeEdges :=
  nonTreeEdges_of_checks cachedMaps (cachedMaps_correct_of_checks hs hm hi hl) h₂ h₃

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.Edges

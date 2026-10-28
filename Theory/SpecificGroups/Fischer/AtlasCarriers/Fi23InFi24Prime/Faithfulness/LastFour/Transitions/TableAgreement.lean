module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Tables
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.TableAgreement.Soundness
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions

/-!
# Assembly boundary for the full-degree word-table agreement

The staged soundness proof reduces the ten literal word interpretations to
four independent numerical certificates. The unconditional `tableAgreement`
remains to be assembled after these certificates are supplied. No table
interpretation, permutation order or stabilizer assertion is assumed as an axiom.

The application below uses the original transition consumer and retains its
independent essential-transition and candidate-comparison premises.
Source: ATLAS F24G1-p306936B0 and GLS3 Table 5.3v.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions

/-- Interpretation of every published generator table from staged certificates. -/
theorem tableAgreement_of_stagedChecks
    (hs : Staged.SeedChecks) (hm : Staged.MiddleChecks)
    (hf : Staged.FrontChecks) (ht : Staged.TailChecks) : TableAgreement :=
  Staged.tableAgreement_of_checks hs hm hf ht

/-- Application at the literal carrier transition boundary. The four numerical
premises must be discharged before asserting unconditional table agreement. -/
theorem stepIdentities_of_compared_candidates_of_stagedChecks
    (ha : candidateA.val = FirstFourModel.aPerm)
    (hb : candidateB.val = FirstFourModel.bPerm)
    (hs : Staged.SeedChecks) (hm : Staged.MiddleChecks)
    (hf : Staged.FrontChecks) (ht : Staged.TailChecks)
    (checks : EssentialChecks) : LastFour.StepIdentities :=
  LastFour.stepIdentities_of_compared_candidates_of_checks ha hb
    (tableAgreement_of_stagedChecks hs hm hf ht) checks

end Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions

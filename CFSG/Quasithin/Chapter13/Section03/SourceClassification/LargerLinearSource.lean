module

public import CFSG.Quasithin.Chapter13.Section03.SourceClassification.LargerLinearInput
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource

/-!
# The guarded larger-linear source consumer

The natural-module branch is now constructed by the completed Section 12.9
source family from the guarded seven-module catalogue.  This adapter feeds that
construction directly to the existing 12.9.1 consumer.  It keeps the two
independent natural reductions and the universal earlier-source record
explicit; no same-ambient `At` record is promoted to a universal theorem.

Source: Aschbacher--Smith 12.9.1 and 13.1.2(3), printed pp.857--866.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceClassification
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section09 Chapter13.Section01
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {I : Subgroup G} {n : ℕ}

/-- The accepted Section 12.9 natural-branch construction supplies the
`NaturalBranchInput` expected by the literal larger-linear exclusion. -/
theorem largerLinear_excluded_of_source_modules
    (h : Hypothesis1311 T)
    (earlier : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (five : NaturalReduction KnownSimple.IsKnownSimple.{u} 5)
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (hi : Hypothesis1223 KnownSimple.IsKnownSimple T I) (hn : n = 4 ∨ n = 5) :
    ¬ ClassicalGroup.IsPSL (I ⧸ pCore 2 I) n 2 :=
  largerLinear_excluded_of_source_inputs h earlier four five
    (NaturalSource.naturalBranchInput_of_modules modules) hi hn

end CFSG.Quasithin.Chapter13.Section03.SourceClassification

module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.LocalFacts
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2

/-!
# Exhaustive double-coset coverage of the Held group

The subgroup splitting and ambient generation are proved for the literal
marking and representatives. The three certified transition columns each
contain 9,662 actual factorization equations. Positive word induction then
shows that every Held element is `s * representative j * t`, with both outer
factors in `markedSubgroup`. The theorem `covers` discharges all three column
premises of the reusable assembly `covers_of_columns`.

Source: the elementary double-coset transition argument in
`Theory.GroupTheory.DoubleCosetTransitions`; source context and data provenance
are recorded in `DoubleCosets/source/README.md`.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets
open Theory.GroupTheory.DoubleCosetTransitions

/-- The first unchanged representative is the identity. -/
public theorem representative_zero : representative 0 = 1 := by
  rw [representative_eq_fast]
  rfl

/-- The three columns suffice; generation and subgroup splitting are discharged. -/
public theorem covers_of_columns
    (h0 : TransitionColumn 0) (h1 : TransitionColumn 1) (h2 : TransitionColumn 2) :
    Covers := by
  apply cover_of_transitions markedSubgroup representative move generation
    ⟨0, representative_zero⟩ middle middle_split
  intro j i e
  refine Fin.cases (h0 j e) (fun i => ?_) i
  refine Fin.cases (h1 j e) (fun i => ?_) i
  exact Fin.cases (h2 j e) (fun k => Fin.elim0 k) i

/-- Every element of the actual Held carrier lies in one of the 4,831
published double cosets of the unchanged marked subgroup. -/
public theorem covers : Covers :=
  covers_of_columns column0 column1 column2

end Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets

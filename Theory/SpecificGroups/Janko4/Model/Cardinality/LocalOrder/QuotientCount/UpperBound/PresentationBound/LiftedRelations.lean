module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.PresentationBound.LiftedRelations.Evaluations
import Mathlib.Tactic.FinCases

/-!
# The fixed stabilizer relations hold in the original presentation

Each of the 43 relations is expanded through the ten fixed generator words.
The resulting words are derived from the original 47 defining relators by
cyclic shifts, inversion, normalization using `x² = y³ = 1`, and elementary
relator rewrites. The adjacent certificate modules contain the explicit proof
DAG. GAP's Tietze snapshots guided discovery only; the proofs use neither the
permutation image nor a finiteness or faithfulness assumption.

See `FirstStabilizer.lean` and `LiftedRelations/source/README.md` for the
source data and reproduction instructions.
-/

public section
namespace Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound

/-- Every fixed auxiliary relation holds on the fixed lifted generators. -/
theorem stabilizer_relations : StabilizerRelations := by
  intro i
  fin_cases i
  · exact LiftedRelations.lifted0
  · exact LiftedRelations.lifted1
  · exact LiftedRelations.lifted2
  · exact LiftedRelations.lifted3
  · exact LiftedRelations.lifted4
  · exact LiftedRelations.lifted5
  · exact LiftedRelations.lifted6
  · exact LiftedRelations.lifted7
  · exact LiftedRelations.lifted8
  · exact LiftedRelations.lifted9
  · exact LiftedRelations.lifted10
  · exact LiftedRelations.lifted11
  · exact LiftedRelations.lifted12
  · exact LiftedRelations.lifted13
  · exact LiftedRelations.lifted14
  · exact LiftedRelations.lifted15
  · exact LiftedRelations.lifted16
  · exact LiftedRelations.lifted17
  · exact LiftedRelations.lifted18
  · exact LiftedRelations.lifted19
  · exact LiftedRelations.lifted20
  · exact LiftedRelations.lifted21
  · exact LiftedRelations.lifted22
  · exact LiftedRelations.lifted23
  · exact LiftedRelations.lifted24
  · exact LiftedRelations.lifted25
  · exact LiftedRelations.lifted26
  · exact LiftedRelations.lifted27
  · exact LiftedRelations.lifted28
  · exact LiftedRelations.lifted29
  · exact LiftedRelations.lifted30
  · exact LiftedRelations.lifted31
  · exact LiftedRelations.lifted32
  · exact LiftedRelations.lifted33
  · exact LiftedRelations.lifted34
  · exact LiftedRelations.lifted35
  · exact LiftedRelations.lifted36
  · exact LiftedRelations.lifted37
  · exact LiftedRelations.lifted38
  · exact LiftedRelations.lifted39
  · exact LiftedRelations.lifted40
  · exact LiftedRelations.lifted41
  · exact LiftedRelations.lifted42

end Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound

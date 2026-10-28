module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.FiniteBound.LiftedRelations.Evaluations
public import Mathlib.Tactic.FinCases

/-!
# All relations of the seven-generator stabilizer lift

The 16 evaluations are proved from the original 29 defining relators by the
word derivations in `LiftedRelations/`. No finite model is assumed.
-/

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound

public theorem liftedRelations01 : LiftedRelations01 := by
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

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.FiniteBound

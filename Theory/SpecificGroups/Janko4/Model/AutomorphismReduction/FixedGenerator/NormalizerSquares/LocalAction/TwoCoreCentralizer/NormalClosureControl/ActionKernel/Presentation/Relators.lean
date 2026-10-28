module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Checked
import Mathlib.Tactic.FinCases

/-!
# Certified lifts of the max2 quotient relators

Shared subwords factor the explicit words in `Presentation.Data`. The original
ATLAS max2 matrices and thirteen normal-closure generators are already checked
in `CentralizerReduction`. Each additional product is checked by kernel reduction
of the proved packed arithmetic; Python supplies witnesses only. The resulting
relator lifts are actual words in the relative normal closure, with no local
identification or order assumed. See `Presentation/source/README.md`.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- Every candidate relator lifts to its certified product in the normal closure. -/
theorem localRelator_matrix_evaluation (i : Fin 29) :
    representation (localRelator i) = Relators.matrixProduct (relatorMask i) := by
  fin_cases i
  · exact Relators.evaluation_0
  · exact Relators.evaluation_1
  · exact Relators.evaluation_2
  · exact Relators.evaluation_3
  · exact Relators.evaluation_4
  · exact Relators.evaluation_5
  · exact Relators.evaluation_6
  · exact Relators.evaluation_7
  · exact Relators.evaluation_8
  · exact Relators.evaluation_9
  · exact Relators.evaluation_10
  · exact Relators.evaluation_11
  · exact Relators.evaluation_12
  · exact Relators.evaluation_13
  · exact Relators.evaluation_14
  · exact Relators.evaluation_15
  · exact Relators.evaluation_16
  · exact Relators.evaluation_17
  · exact Relators.evaluation_18
  · exact Relators.evaluation_19
  · exact Relators.evaluation_20
  · exact Relators.evaluation_21
  · exact Relators.evaluation_22
  · exact Relators.evaluation_23
  · exact Relators.evaluation_24
  · exact Relators.evaluation_25
  · exact Relators.evaluation_26
  · exact Relators.evaluation_27
  · exact Relators.evaluation_28

/-- All 29 relators belong to the actual relative seed normal closure. -/
theorem localRelator_mem (i : Fin 29) : localRelator i ∈ localNormalClosure :=
  Relators.relator_mem_of_matrix_evaluation i (localRelator_matrix_evaluation i)

/-- The remaining upper-bound obligation concerns only the explicit presentation. -/
theorem quotient_card_le_of_presentation_bound
    (hbound : Finite Group ∧ Nat.card Group ≤ 2661120) :
    Nat.card LocalNormalClosureQuotient ≤ 2661120 :=
  quotient_card_le_of_relators localRelator_mem hbound

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation

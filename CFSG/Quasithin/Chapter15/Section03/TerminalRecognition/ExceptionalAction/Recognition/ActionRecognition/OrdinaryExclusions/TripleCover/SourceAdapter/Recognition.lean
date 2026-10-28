module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.TripleCover.SourceAdapter.SourceCover
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.TripleCover.SourceAdapter.Consumer

/-!
# Discharging the terminal source cover comparison

The full surviving source quotient and source-correct FF alternative now
feed ExceptionalCase without a separate cover-comparison premise. The
literal SourceInput, offender representation and all module hypotheses
remain unchanged. The universal source classifications and the subsequent
six-dimensional representation recognition retain their existing owners.

Source: final proof of Aschbacher--Smith 15.3.1, printed p.1155.
-/

public section

open Subgroup Atlas.Codes Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.TripleCover.SourceAdapter

open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

variable {H : Type*} [Group H] [Finite H]
  {V : Subgroup H} [IsElementaryAbelian 2 (moduleClosure V)]

/-- The actual source alternatives suffice, with the cubic-cover comparison
proved from the existing source contract. -/
theorem exceptionalCase_of_surviving_source_models (d : SourceInput V)
    (quotient : Cases.SurvivingQuotientAlternative (coreQuotient H))
    (h : Intersection.SourceFFAlternative d.offenderAction) :
    Nonempty (ExceptionalCase d) :=
  exceptionalCase_of_surviving_source d quotient h
    FSource.TripleSymmetric.nonempty_hexacode_equiv

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.TripleCover.SourceAdapter

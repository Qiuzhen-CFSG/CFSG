module

public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.PreparationInput

/-!
# Applying the derived B.5.5 preparation to the B.5.6 cover construction

The existing high-three-rank construction uses B.5.5 to prove positive
three-rank for every component through its literal chief-section projection
and to obtain the exact generalized-Fitting identity. This application
discharges its entire `Preparation.ComponentInput` with the source theorem.
It keeps the original action, selected component and lifted-cover conclusion.

The four earlier preparation implications have the producers documented in
`PreparationSource`. The cover construction additionally retains the genuine
B.5.2 implication (`qt-b05-quotient-components`) and its independent I.1.3
multiplier bound (`qt-i-01`). The A.2 input is shared with preparation.
Final discharge for B.5.6 remains with `qt-b05-general-classification`;
the preparation theorem itself requires no multiplier input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.5 and the B.5.7 reduction in the proof of B.5.6, printed pp.104–106.
-/

public section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.PreparationSource.Application
open SourceInduction HighThreeRank.CoverCentralizer
universe u v

/-- The actual B.5.6 cover consumer with its B.5.5 assumption discharged by
the complete preparation theorem, using the original section quotient maps. -/
theorem exists_liftedCover_of_source
    {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {K : GroupClass.{u}}
    (hn : ComponentNormalizationInput.{u,v})
    (hA : SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (h52 : SourceConstruction.CoverInput K)
    (hI : SourceConstruction.MultiplierInput K)
    (hyp : FFHypothesis K ρ) {L : Subgroup D}
    (hL : IsComponent D L) (hrL : 1 < primeRank 3 L) :
    Nonempty (LiftedCover K D L) :=
  SourceConstruction.exists_liftedCover_of_preparation ρ h52
    (componentInput hn hA h36 h4) hA hI hyp hL hrL

end CFSG.Quasithin.ChapterB.PreparationSource.Application

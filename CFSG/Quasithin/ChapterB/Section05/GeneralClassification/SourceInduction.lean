module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.PreparationInput
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Descent
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.OuterFixedLine
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.CounterexampleReduction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.SymmetricThreeModule
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Assembly

/-!
# Source induction for the separate adequate B.5.6 target

`SourceInduction.AdequateAlternative` retains the trivial actor and the full
source group-and-module outputs except for the separately specified outer
A₆–C₃ shape. Its B.5.1 clause uses the corrected projective-line convention.
The older whole-space splitting obstruction remains available unchanged.

The completed reductions include:
* all B.5.3 hypotheses and strict descent for the actual complementary factor,
  for both the supplement and exceptional hyperplane branches;
* the high-three-rank alternative B.5.7 and component reductions B.5.9–10,
  under their complete universal earlier-source implications;
* B.5.11(1), including nontriviality of the complementary factor under the
  genuine counterexample hypothesis;
* comparison of all adequate alternatives at three-rank at most one, retaining
  the full surviving B.5.1 or S₃ action and the rank-one B.5.1 action rows;
* the complete S₃ factor-module extraction, using the actual faithful binary
  plane action and its quotient image;
* the fixed-quotient decomposition in B.5.12.

`exceptional_configuration_of_preparation` assembles B.5.8--12,
supplying Fitting centralization and factor-module extraction from their proved
source reductions. It invokes induction only on the strictly smaller
centralizer acting on C_V(G₁). All selected-factor, complementary-rank and
extraction premises are discharged. The same B.5.5 input supplies the high-rank
and component arguments; no second classifier presentation is required. The
older two-input APIs remain available. The split exceptional branch and the
actual second-four-space complement and two-factor application are also proved.

`adequateClassification_of_source` completes the conditional adequate
classification by strong induction on the actual group order. It supplies the
literal second factor module to the completed exceptional endgame, including
the ordinary nonsplit cohomology branch. No recursive-classification,
counterexample-reduction, extraction or splitting premise remains.
`FFHypothesis.adequate_of_source` applies this theorem to the original action,
and `FFHypothesis.nontrivial_adequate_of_source` removes the trivial branch for
a nontrivial actor. These theorems establish the adopted adequate target;
the original whole-space outer splitting remains separate and unchanged.

The assembled component recursion uses exactly the complete universal B.5.1,
B.5.2, B.5.5 (through the existing preparation chief-section input), A.2.1,
I.1.3 and B.4.8(2) implications. The fitting and exceptional arguments also use
the genuine B.1.9, A.1.31(1) and B.4.8(3--4) implications. Their producers are
qt-b05-quasisimple, qt-b05-quotient-components, qt-a-02, qt-i-01,
qt-b01-fitting-structure, qt-a-01-section-rank and
qt-b-04-natural-extensions. Instantiation of these ten earlier-source inputs
with the full known-simple catalogue remains with qt-b05-general-classification.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.3 and B.5.6–12, printed pp.104–110.
-/

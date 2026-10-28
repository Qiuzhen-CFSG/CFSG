module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.NormalizedSourceInputs
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.Complete
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.DualExtensions.RootPairGeometry

/-!
# Adequate B.5 from the genuine earlier classification theorems

The complete B.5.1 induction supplies all six quasisimple source clauses.
The actual natural G₂ offender theorem supplies its last root-pair input,
with the same two root groups and conjugator. Thus the adequate B.5.6
classification depends only on the genuine semisimplicity, A.3.6 and
corrected B.4.2 theorems. No quasisimple or adequate classification conclusion
is an additional premise, and every module and outer-action alternative
of the existing adequate target is retained.

Source: Aschbacher--Smith, B.5.1--12, printed pp.99--110, and B.4.6(13).
-/

public section
namespace CFSG.Quasithin.ChapterB.SourceInduction
open HighThreeRank.CoverCentralizer.SourceConstruction
open QuasisimpleSource.SourceCompletion
universe u v

/-- The original B.4.6 root-pair theorem supplies the precise B.5.1 input. -/
theorem nonbinaryG2RootPairInput : NonbinaryG2RootPairInput :=
  fun F _ => QuasisimpleSource.ExtensionConsequences.DualExtensions.g2_bestOffender_rootPair F

/-- Full adequate B.5, with the complete B.5.1 source induction discharged. -/
theorem adequateClassification_knownSimple_of_earlier_classification
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple) :
    AdequateClassificationInput.{u,v} KnownSimple.IsKnownSimple :=
  adequateClassification_knownSimple_of_classification_theorems
    (knownSimple_quasisimpleClassificationInput hA h36 h4 nonbinaryG2RootPairInput)
    hA h36 h4

/-- Literal application to the original faithful FF action. All adequate
module alternatives are retained, including the trivial actor allowed by B.5.3. -/
theorem adequateAlternative_of_earlier_classification
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple)
    {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (h : FFHypothesis KnownSimple.IsKnownSimple ρ) :
    AdequateAlternative ρ :=
  adequateClassification_knownSimple_of_earlier_classification hA h36 h4 D V ρ h

/-- The actual nontrivial actor supplies the nontrivial B.5.6 alternatives. -/
theorem nontrivialAdequateAlternative_of_earlier_classification
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple)
    {D : Type u} [Group D] [Finite D] [Nontrivial D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (h : FFHypothesis KnownSimple.IsKnownSimple ρ) :
    NontrivialAdequateAlternative ρ :=
  (adequateAlternative_of_earlier_classification hA h36 h4 ρ h).of_nontrivial ρ

end CFSG.Quasithin.ChapterB.SourceInduction

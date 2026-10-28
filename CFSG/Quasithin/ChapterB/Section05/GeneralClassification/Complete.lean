module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.KnownSimpleSources
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Complete

/-!
# Complete adequate B.5 classification

The original corrected B.4.2 theorem supplies the final earlier input to the
complete B.5 source induction. The complete known-simple catalogue is fixed,
and no classification, cover, geometry or model-realization input remains.
Every adequate module and outer-action alternative is retained, including
the trivial actor allowed by B.5.3 and the nontrivial B.5.6 conclusion.
Source: Aschbacher--Smith B.5.1--12, printed pp.99--110.
-/

public section
namespace CFSG.Quasithin.ChapterB.SourceInduction
universe u v

theorem adequateClassification_knownSimple :
    AdequateClassificationInput.{u,v} KnownSimple.IsKnownSimple :=
  adequateClassification_knownSimple_of_b4 SourceClassification.irreducibleClassification_knownSimple

/-- The literal original faithful FF action has the complete adequate alternatives. -/
theorem adequateAlternative_knownSimple
    {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (h : FFHypothesis KnownSimple.IsKnownSimple ρ) :
    AdequateAlternative ρ :=
  adequateClassification_knownSimple D V ρ h

/-- Nontriviality eliminates precisely the trivial actor alternative. -/
theorem nontrivialAdequateAlternative_knownSimple
    {D : Type u} [Group D] [Finite D] [Nontrivial D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (h : FFHypothesis KnownSimple.IsKnownSimple ρ) :
    NontrivialAdequateAlternative ρ :=
  (adequateAlternative_knownSimple ρ h).of_nontrivial ρ

end CFSG.Quasithin.ChapterB.SourceInduction

module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.ExtensionClauses
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SQTKSectionImage

/-!
# Complete source B.5.1 in the irreducible moved-section branch

The original finite faithful action and Fitting hypotheses give the complete
corrected B.5.1(1i) alternative. The extension assembly supplies all five
subsequent clauses, including the literal Sylow-fixed centralizer. Specializing
to the full known-simple catalogue discharges the simple-two-group class input.

Two genuine earlier-source inputs remain: full universal B.4.2 with the
projective-line convention, and nonbinary G₂ root-pair placement in best
offenders. The latter is used only in the supplement conclusion. The remaining
reducible B.5.1 induction is a separate mathematical obligation, not assumed
as an input of the branch theorem below.

Source: Aschbacher--Smith, combined manuscript, B.5.1, pp.99--103.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}} {L : Subgroup G}

/-- All six corrected B.5.1 clauses when the actual moved section belongs to
Irr⁺. No action alternative, splitting assertion, or B.5 classifier is assumed. -/
theorem irreducible_conclusion
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hroot : NonbinaryG2RootPairInput)
    (h : QuasisimpleSourceHypothesis ρ K L)
    (hi : IsIrrPlus ρ L (moved ρ L)) :
    Nonempty (SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L) := by
  let s : MovedSection ρ L := QuasisimpleSourceHypothesis.movedSection ρ h
  have hs : IsIrrPlus ρ L s.space.toSubmodule := s.space_eq.symm ▸ hi
  obtain ⟨hfit, hc⟩ := h.irreducible_source_case earlier hK s hs
  exact ⟨conclusion_of_action hroot h s hfit hc⟩

/-- The actual full known-simple-catalogue application. Only the two named
earlier Chapter B source inputs and the genuine irreducible branch remain. -/
theorem knownSimple_irreducible_conclusion
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v}
      KnownSimple.IsKnownSimple)
    (hroot : NonbinaryG2RootPairInput)
    (h : QuasisimpleSourceHypothesis ρ KnownSimple.IsKnownSimple L)
    (hi : IsIrrPlus ρ L (moved ρ L)) :
    Nonempty (SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L) :=
  irreducible_conclusion earlier
    ComponentRecognition.SQTKSectionImage.knownSimple_containsSimpleTwoGroups hroot h hi

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion

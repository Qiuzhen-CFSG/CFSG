module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SourceB5.Coordinates

/-!
# All six quasisimple B.5 clauses on the original Chapter 15 action

Every corrected irreducible case and every moved-section alternative is
transported through the literal coordinate maps. The six source clauses,
including nonsplit, homogeneous, supplement and centralizer assertions,
are preserved. The input conversion retains the same generalized Fitting
subgroup and the complete original SQTK hypothesis.

Source: Aschbacher--Smith B.5.1, printed pp.99--103.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.SourceB5
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}

theorem irreducible {L H : Subgroup D}
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) :
    ProjectiveLine.IrreducibleActionCase ρ L H := by
  cases h with
  | linearTwo F h e ho hr => exact .linearTwo (field F) h (action e) ho hr
  | linearThree F h e hr => exact .linearThree (field F) h (action e) hr
  | symplectic F hdeg h e hr => exact .symplectic (field F) hdeg h (action e) hr
  | symplecticTwo e hr => exact .symplecticTwo (marked e) hr
  | g2 F hdeg h e ho hr => exact .g2 (field F) hdeg h (action e) ho hr
  | g2Two e ho hr => exact .g2Two (marked e) ho hr
  | symmetric n hn e ho hr => exact .symmetric n hn (marked e) ho hr
  | alternatingSix h e ho hr => exact .alternatingSix h (action e) ho hr
  | alternatingSeven h ht e hd ho hr => exact .alternatingSeven h ht e hd ho hr
  | tripleSix h e hr => exact .tripleSix h (tripleSix e) hr
  | binaryLinear d hd h e hr => exact .binaryLinear d hd h (action e) hr
  | orthogonalSix h ht e ho hr => exact .orthogonalSix h ht (action e) ho hr
  | symmetricEight h e hr => exact .symmetricEight h (marked e) hr
  | exteriorFive h ht e hd ho hr => exact .exteriorFive h ht e hd ho hr

theorem outer (h : ChapterB.QuasisimpleSource.OuterNaturalAction ρ) : OuterNaturalAction ρ := by
  rcases h with h | h
  · obtain ⟨n,hlo,hhi,⟨e⟩⟩ := h
    exact Or.inl ⟨n,hlo,hhi,⟨action e⟩⟩
  · obtain ⟨e⟩ := h
    exact Or.inr ⟨action e⟩

theorem quasisimpleCase {L : Subgroup D} {s : Low.MovedSection ρ L}
    (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) :
    ProjectiveLine.QuasisimpleActionCase ρ L (movedSection s) := by
  cases h with
  | irreducible hi hf hir h he =>
    refine .irreducible hi hf hir (irreducible h) ?_
    exact he.imp id (fun h => ⟨h.1,outer h.2⟩)
  | doubleThree F hw e ho hr => exact .doubleThree (field F) hw (action e) ho hr
  | naturalDual d hd hw hn => obtain ⟨e⟩ := hn; exact .naturalDual d hd hw ⟨action e⟩
  | repeatedNatural d r hd hr hb hw hn =>
    obtain ⟨e⟩ := hn
    exact .repeatedNatural d r hd hr hb hw ⟨action e⟩

def quasisimpleConclusion [Finite D] {L : Subgroup D}
    (s : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L) :
    ProjectiveLine.QuasisimpleSourceConclusion ρ L where
  sectionData := movedSection s.sectionData
  fitting_eq := s.fitting_eq
  clause_one := quasisimpleCase s.clause_one
  nonsplitting_iff := s.nonsplitting_iff
  clause_two := fun h => ⟨(s.clause_two h).1,nonsplit (s.clause_two h).2⟩
  clause_three := by
    rcases s.clause_three with h | ⟨d,hd,⟨e⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨d,hd,⟨action e⟩⟩
  clause_four := by
    intro h
    obtain ⟨hi,hs⟩ := s.clause_four h
    refine ⟨hi,?_⟩
    rcases hs with h | ⟨hc,hn,hd⟩
    · exact Or.inl h
    · refine Or.inr ⟨hc,?_,hd⟩
      rcases hn with h | h
      · obtain ⟨e⟩ := h; exact Or.inl ⟨action e⟩
      · obtain ⟨e⟩ := h; exact Or.inr ⟨action e⟩
  clause_five := s.clause_five.imp id (fun h => ⟨h.1,supplement h.2.1,h.2.2⟩)
  clause_six := by
    intro d hd hw hn T
    obtain ⟨e⟩ := hn
    obtain ⟨h⟩ := s.clause_six d hd hw ⟨actionBack e⟩ T
    exact ⟨sylowFixed h⟩

theorem quasisimpleInput {K : GroupClass.{u}}
    (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleClassificationInput.{u,v} K) :
    ProjectiveLine.QuasisimpleClassificationInput.{u,v} K := by
  intro D _ _ V _ _ ρ L hyp
  obtain ⟨s⟩ := h D V ρ L ⟨hyp.finite_module,hyp.faithful,hyp.quasisimple,hyp.sqtk,
    hyp.fitting,hyp.twoCore,hyp.generated⟩
  exact ⟨quasisimpleConclusion s⟩
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.SourceB5

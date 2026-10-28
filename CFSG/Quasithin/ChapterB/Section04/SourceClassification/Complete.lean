module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Triality.RemainingSource
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Triality.Complete
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.SourceCatalogue

/-!
# Complete original B.4.2 classification

Unconditional Theorems A and C provide the full known-simple central-quotient
catalogue. All source representation families are classified; the genuine
triality exclusion discharges the final even-exponent proper-extension branch.
The corrected target preserves every original module and offender alternative.
Source: Aschbacher--Smith B.4.2, printed p.86 and Chapter K.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceClassification
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem actionCase_of_source (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hff : IsFFModule ρ) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  rcases source_case_or_even_triality h hff with hcase | ⟨n,hn,_,hm⟩
  · exact hcase
  · exact (triality_not_ff h n hn hm hff).elim

/-- B.4.2 on its literal original best-offender hypotheses. -/
theorem actionCase_of_bestOffender
    (hsq : IsSQTK KnownSimple.IsKnownSimple G) (hfit : generalizedFitting G = L)
    (hL : IsQuasisimple L) (hf : Function.Injective ρ)
    (hi : IsIrreducible (ρ.comp L.subtype)) {A : Subgroup G} (hA : IsBestOffender ρ A) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) :=
  actionCase_of_source (source_hypotheses_of_bestOffender hsq hfit hL hf hi hA)
    ⟨A,hA.isOffender ρ⟩

/-- The complete earlier-source classification used by B.5, over all known simples. -/
theorem irreducibleClassification_knownSimple :
    SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple := by
  intro G _ _ V _ _ _ ρ hsq hL hf hi hbest
  obtain ⟨A,hA⟩ := hbest
  exact actionCase_of_bestOffender hsq rfl hL hf hi hA

end CFSG.Quasithin.ChapterB.SourceClassification

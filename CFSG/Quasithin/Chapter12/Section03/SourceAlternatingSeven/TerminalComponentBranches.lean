module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentPreparation
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Definitions

/-!
# Remaining source boundaries for the A₅ component

`ResidualAnalysis` is the nonsolvable slice of 12.2.7. Its overgroup clause
applies to the maximal component above the point-centralizer component,
so it must retain that same overgroup, rather than choose an unrelated one.
In the maximal case its action clause permits one or two natural summands;
it does not assert the single-module conclusion of 12.3.12.

The proper-overcomponent and maximal-component arguments can therefore be
proved independently. The assembly below constructs relative normality
using the actual containing component, and retains both action premises
until those source arguments discharge them.
Source: Aschbacher--Smith, 12.2.7, pp.797--798, and 12.3.12, p.811.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

/-- The natural action through the literal residual quotient. -/
abbrev residualNaturalAction (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) :=
  (BinaryPermutation.alternatingCoreRepresentation (Fin 5)).comp
    (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.K)))

/-- The same chosen residual has one or two whole natural summands. Both
alternatives use a zero kernel and the same quotient marking. -/
def AtMostTwoNatural (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) : Prop :=
  Nonempty (Representation.BinaryConjugationSection P.K ⁅P.Z, P.K⁆ ⊥
    (P.residualNaturalAction q)) ∨
  Nonempty (Representation.BinaryConjugationSection P.K ⁅P.Z, P.K⁆ ⊥
    (Representation.prod (P.residualNaturalAction q) (P.residualNaturalAction q)))

/-- The nonsolvable part of 12.2.7 needed at the actual terminal point.
Its construction is an outstanding earlier-source obligation. -/
structure ResidualAnalysis where
  local_mem : P.K ∈ Chapter1.L G (T : Subgroup G)
  quotient : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)
  overgroups : ∀ Y : Subgroup G, Y ∈ Chapter1.LStar G (T : Subgroup G) → P.K ≤ Y →
    ChapterA.Section04.IsFaithfulSignalizerType Y ∧
      (P.K = Y ∨ ∃ W : Subgroup G, Nonempty (Setup T Y W))
  maximal_natural : P.K ∈ Chapter1.LStar G (T : Subgroup G) →
    P.AtMostTwoNatural quotient

/-- Only the action conclusions remain after relative normality is established. -/
def ResidualActionConclusions
    (q : (P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) : Prop :=
  ⁅P.K, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ = P.K ∧
    Nonempty (Representation.BinaryConjugationSection P.K ⁅P.Z, P.K⁆ ⊥
      (P.residualNaturalAction q))

/-- Conditional final assembly of the genuine 12.3.12 conclusions. The
source producer must still construct R and prove both displayed branches. -/
theorem componentAnalysis_of_source_branches (R : P.ResidualAnalysis)
    (properStep : ∀ F : P.Overcomponents, P.K < F.Y →
      (∃ W : Subgroup G, Nonempty (Setup T F.Y W)) →
      F.E = P.K ∧ P.ResidualActionConclusions R.quotient)
    (maximalStep : FaithfulMaximalLocal T P.K →
      P.AtMostTwoNatural R.quotient → P.ResidualActionConclusions R.quotient) :
    Nonempty P.ComponentAnalysis := by
  obtain ⟨F⟩ := P.overcomponents_nonempty R.local_mem
  have hKY : P.K ≤ F.Y := F.residual_le.trans F.le_maximal
  by_cases he : P.K = F.Y
  · have hmax : P.K ∈ Chapter1.LStar G (T : Subgroup G) := he.symm ▸ F.maximal
    obtain ⟨hJ, ⟨hnat⟩⟩ := maximalStep
      ⟨hmax, (R.overgroups P.K hmax le_rfl).1⟩ (R.maximal_natural hmax)
    exact ⟨⟨P.pointCentralizer_normalizes_of_maximal hmax, R.quotient, hJ, hnat⟩⟩
  · have hsetup := (R.overgroups F.Y F.maximal hKY).2.resolve_left he
    obtain ⟨hE, hJ, ⟨hnat⟩⟩ := properStep F (lt_of_le_of_ne hKY he) hsetup
    exact ⟨⟨hE ▸ F.normalizes, R.quotient, hJ, hnat⟩⟩

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperModels
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentModel
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentProperExterior

/-!
# TerminalComponentProperModels at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentProperModels`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
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

theorem componentAnalysis_of_restricted_proper_models_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (localAnalysis_at : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (proper : ∀ (Y : Subgroup G), Y ∈ Chapter1.LStar G (T : Subgroup G) → P.K < Y →
      ∀ (W : Subgroup G) (E : ChosenModule T Y W), ProperOvercomponentAlternatives E →
        Nonempty ((P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) ∧
          (letI := E.actionCentralizer_normal;
            Nonempty ((Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃*
              alternatingGroup (Fin 7)))) :
    Nonempty P.ComponentAnalysis := by
  apply P.componentAnalysis_of_proper_models_at structural modules escape localAnalysis_at hr hw
  intro Y hY hKY
  have h := P.residual_overgroup_hypothesis_at structural modules hr hw hY hKY.le
  obtain ⟨W, ⟨E⟩⟩ := (structural Y h).2.1
  obtain ⟨hK, ⟨e⟩⟩ := proper Y hY hKY W E
    (P.proper_overcomponent_alternatives_at structural modules hr hw hY hKY E)
  exact ⟨hK, P.proper_overcomponent_seven_central_quotient_at
    structural modules hr hw hY hKY E e⟩

theorem componentAnalysis_of_nonnatural_proper_models_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (localAnalysis_at : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (proper : ∀ (Y : Subgroup G), Y ∈ Chapter1.LStar G (T : Subgroup G) → P.K < Y →
      ∀ (W : Subgroup G) (E : ChosenModule T Y W), ProperOvercomponentNonnaturalAlternatives E →
        Nonempty ((P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) ∧
          (letI := E.actionCentralizer_normal;
            Nonempty ((Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃*
              alternatingGroup (Fin 7)))) :
    Nonempty P.ComponentAnalysis := by
  apply P.componentAnalysis_of_proper_models_at structural modules escape localAnalysis_at hr hw
  intro Y hY hKY
  have h := P.residual_overgroup_hypothesis_at structural modules hr hw hY hKY.le
  obtain ⟨W, ⟨E⟩⟩ := (structural Y h).2.1
  obtain ⟨hK, ⟨e⟩⟩ := proper Y hY hKY W E
    (P.proper_overcomponent_nonnatural_alternatives_at structural modules hr hw hY hKY E)
  exact ⟨hK, P.proper_overcomponent_seven_central_quotient_at
    structural modules hr hw hY hKY E e⟩

theorem componentAnalysis_of_alternating_proper_models_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (localAnalysis_at : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (proper : ∀ (Y : Subgroup G), Y ∈ Chapter1.LStar G (T : Subgroup G) → P.K < Y →
      ∀ (W : Subgroup G) (E : ChosenModule T Y W), ProperOvercomponentAlternatingAlternatives E →
        Nonempty ((P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) ∧
          (letI := E.actionCentralizer_normal;
            Nonempty ((Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃*
              alternatingGroup (Fin 7)))) :
    Nonempty P.ComponentAnalysis := by
  apply P.componentAnalysis_of_proper_models_at structural modules escape localAnalysis_at hr hw
  intro Y hY hKY
  have h := P.residual_overgroup_hypothesis_at structural modules hr hw hY hKY.le
  obtain ⟨W, ⟨E⟩⟩ := (structural Y h).2.1
  obtain ⟨hK, ⟨e⟩⟩ := proper Y hY hKY W E
    (P.proper_overcomponent_alternating_alternatives_at structural modules hr hw hY hKY E)
  exact ⟨hK, P.proper_overcomponent_seven_central_quotient_at
    structural modules hr hw hY hKY E e⟩

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven


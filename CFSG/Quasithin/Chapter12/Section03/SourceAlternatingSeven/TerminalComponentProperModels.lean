module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperExterior
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentModel

/-!
# Application of the proper-overcomponent restriction

Choose the source module of each proper maximal overcomponent and apply the
proved restriction of its seven-module alternatives. This connects the case
reduction to all fields of the terminal component analysis. The remaining
recognition premise now concerns only the surviving A₇ and A₈ rows.
The faithful A₇ marking automatically gives the required central quotient
through its proved kernel comparison. Discharge of the remaining premise
and the final 12.3.12 assembly remain with
qt-d-1231-terminal-component.

Source: Aschbacher–Smith, 12.2.7, printed pp.797–798, and 12.3.12, p.811.
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

/-- The surviving source cases suffice for the original component-analysis
consumer. The residual marking is still a mathematical obligation. -/
theorem componentAnalysis_of_restricted_proper_models
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (localAnalysis : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (proper : ∀ (Y : Subgroup G), Y ∈ Chapter1.LStar G (T : Subgroup G) → P.K < Y →
      ∀ (W : Subgroup G) (E : ChosenModule T Y W), ProperOvercomponentAlternatives E →
        Nonempty ((P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) ∧
          (letI := E.actionCentralizer_normal;
            Nonempty ((Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃*
              alternatingGroup (Fin 7)))) :
    Nonempty P.ComponentAnalysis := by
  apply P.componentAnalysis_of_proper_models structural modules escape localAnalysis hr hw
  intro Y hY hKY
  have h := P.residual_overgroup_hypothesis structural modules hr hw hY hKY.le
  obtain ⟨W, ⟨E⟩⟩ := (structural G T Y h).2.1
  obtain ⟨hK, ⟨e⟩⟩ := proper Y hY hKY W E
    (P.proper_overcomponent_alternatives structural modules hr hw hY hKY E)
  exact ⟨hK, P.proper_overcomponent_seven_central_quotient
    structural modules hr hw hY hKY E e⟩

/-- The natural linear rows are discharged. The exterior and alternating
recognition input remains with the terminal-component assembly owner. -/
theorem componentAnalysis_of_nonnatural_proper_models
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (localAnalysis : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (proper : ∀ (Y : Subgroup G), Y ∈ Chapter1.LStar G (T : Subgroup G) → P.K < Y →
      ∀ (W : Subgroup G) (E : ChosenModule T Y W), ProperOvercomponentNonnaturalAlternatives E →
        Nonempty ((P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) ∧
          (letI := E.actionCentralizer_normal;
            Nonempty ((Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃*
              alternatingGroup (Fin 7)))) :
    Nonempty P.ComponentAnalysis := by
  apply P.componentAnalysis_of_proper_models structural modules escape localAnalysis hr hw
  intro Y hY hKY
  have h := P.residual_overgroup_hypothesis structural modules hr hw hY hKY.le
  obtain ⟨W, ⟨E⟩⟩ := (structural G T Y h).2.1
  obtain ⟨hK, ⟨e⟩⟩ := proper Y hY hKY W E
    (P.proper_overcomponent_nonnatural_alternatives structural modules hr hw hY hKY E)
  exact ⟨hK, P.proper_overcomponent_seven_central_quotient
    structural modules hr hw hY hKY E e⟩

/-- Every linear row is discharged. Recognition of the alternating rows
remains with the terminal-component assembly owner. -/
theorem componentAnalysis_of_alternating_proper_models
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (localAnalysis : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G))
    (proper : ∀ (Y : Subgroup G), Y ∈ Chapter1.LStar G (T : Subgroup G) → P.K < Y →
      ∀ (W : Subgroup G) (E : ChosenModule T Y W), ProperOvercomponentAlternatingAlternatives E →
        Nonempty ((P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) ∧
          (letI := E.actionCentralizer_normal;
            Nonempty ((Y ⧸ (centralizer (W : Set G)).subgroupOf Y) ≃*
              alternatingGroup (Fin 7)))) :
    Nonempty P.ComponentAnalysis := by
  apply P.componentAnalysis_of_proper_models structural modules escape localAnalysis hr hw
  intro Y hY hKY
  have h := P.residual_overgroup_hypothesis structural modules hr hw hY hKY.le
  obtain ⟨W, ⟨E⟩⟩ := (structural G T Y h).2.1
  obtain ⟨hK, ⟨e⟩⟩ := proper Y hY hKY W E
    (P.proper_overcomponent_alternating_alternatives structural modules hr hw hY hKY E)
  exact ⟨hK, P.proper_overcomponent_seven_central_quotient
    structural modules hr hw hY hKY E e⟩

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

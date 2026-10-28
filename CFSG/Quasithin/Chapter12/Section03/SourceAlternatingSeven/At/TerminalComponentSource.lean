module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentSource
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentProperSeven

/-!
# TerminalComponentSource at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentSource`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

theorem residual_quotient_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (localAnalysis_at : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    Nonempty ((P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) := by
  by_cases hm : P.K ∈ Chapter1.LStar G (T : Subgroup G)
  · exact (P.maximal_residual_five_at structural modules hr hw hm).1
  obtain ⟨F,_⟩ := P.overcomponents_of_original_at structural modules hr hw
  have hKY : P.K < F.Y := lt_of_le_of_ne (F.residual_le.trans F.le_maximal)
    (fun he => hm (he.symm ▸ F.maximal))
  obtain ⟨W,⟨SY⟩⟩ := P.proper_overcomponent_setup_at structural modules hr hw F.maximal hKY
  obtain ⟨DY⟩ := localAnalysis_at F.Y W SY
  exact P.proper_residual_five_at structural modules escape hr hw hKY SY DY

theorem componentAnalysis_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (localAnalysis_at : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    Nonempty P.ComponentAnalysis := by
  obtain ⟨q⟩ := P.residual_quotient_source_at structural modules escape localAnalysis_at hr hw
  exact P.componentAnalysis_of_residual_quotient_at structural modules escape localAnalysis_at hr hw q

theorem residualAnalysis_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (localAnalysis_at : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    Nonempty P.ResidualAnalysis := by
  obtain ⟨A⟩ := P.componentAnalysis_source_at structural modules escape localAnalysis_at hr hw
  refine ⟨⟨(P.residual_local_and_quasisimple_at structural modules hr hw).1,
    A.quotient,?_,fun _ => Or.inl ⟨A.natural⟩⟩⟩
  intro Y hY hKY
  refine ⟨(P.residual_overgroup_hypothesis_at structural modules hr hw hY hKY).maximal_faithful.2,?_⟩
  by_cases he : P.K = Y
  · exact Or.inl he
  · exact Or.inr (P.proper_overcomponent_setup_at structural modules hr hw hY (lt_of_le_of_ne hKY he))

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven


module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperSeven

/-!
# The original terminal component analysis, 12.3.12

Recognize the actual residual K = O²(H) inside a maximal overcomponent.
The maximal branch supplies its A₅ quotient and full natural module.
Every proper overcomponent has the original A₇ setup; its local analysis,
full symmetric action and minimal parabolicity identify the same residual
quotient as A₅, retaining the possible central cover of the overcomponent.

The earlier proper-component argument now applies without a recognition
premise. It proves normality relative to the actual point centralizer,
Thompson generation, and the binary augmentation action on the entire
[Z,K] through that same quotient. Only the terminal parent's original
structural, module, escape, local-analysis and strict r,w inputs remain.

Source: Aschbacher–Smith 12.3.12, printed p.811, using the nonsolvable
slice of 12.2.7, pp.797–798, and 12.3.7, p.809. The final 12.3.1
contradiction remains with the terminal assembly owner.
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

/-- The original escaping residual has the literal A₅ quotient, with no
residual or overcomponent model assumed. -/
theorem residual_quotient_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (localAnalysis : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    Nonempty ((P.K ⧸ pCore 2 P.K) ≃* alternatingGroup (Fin 5)) := by
  by_cases hm : P.K ∈ Chapter1.LStar G (T : Subgroup G)
  · exact (P.maximal_residual_five structural modules hr hw hm).1
  obtain ⟨F,_⟩ := P.overcomponents_of_original structural modules hr hw
  have hKY : P.K < F.Y := lt_of_le_of_ne (F.residual_le.trans F.le_maximal)
    (fun he => hm (he.symm ▸ F.maximal))
  obtain ⟨W,⟨SY⟩⟩ := P.proper_overcomponent_setup structural modules hr hw F.maximal hKY
  obtain ⟨DY⟩ := localAnalysis F.Y W SY
  exact P.proper_residual_five structural modules escape hr hw hKY SY DY

/-- All genuine conclusions of 12.3.12 from the original terminal inputs. -/
theorem componentAnalysis_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (localAnalysis : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    Nonempty P.ComponentAnalysis := by
  obtain ⟨q⟩ := P.residual_quotient_source structural modules escape localAnalysis hr hw
  exact P.componentAnalysis_of_residual_quotient structural modules escape localAnalysis hr hw q

/-- The nonsolvable residual boundary is also realized on the actual terminal
point, including every maximal overcomponent and the whole moved module. -/
theorem residualAnalysis_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (localAnalysis : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) :
    Nonempty P.ResidualAnalysis := by
  obtain ⟨A⟩ := P.componentAnalysis_source structural modules escape localAnalysis hr hw
  refine ⟨⟨(P.residual_local_and_quasisimple structural modules hr hw).1,
    A.quotient,?_,fun _ => Or.inl ⟨A.natural⟩⟩⟩
  intro Y hY hKY
  refine ⟨(P.residual_overgroup_hypothesis structural modules hr hw hY hKY).maximal_faithful.2,?_⟩
  by_cases he : P.K = Y
  · exact Or.inl he
  · exact Or.inr (P.proper_overcomponent_setup structural modules hr hw hY (lt_of_le_of_ne hKY he))

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

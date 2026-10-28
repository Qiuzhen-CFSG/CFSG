module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalSource
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentSource
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductComplete

/-!# The terminal A₇ contradiction from the earlier source inputs

Choose the actual central weight-four point and its escaping H-star subgroup.
The component argument constructs the normal A₅ residual K = O²(H), with
Thompson generation and its full binary natural module. The product argument
then proves the central-cover reduction and constructs the literal
Y = KL₂T and U = ⟨Z^Y⟩, with their marked S₅ × S₃ quotient action.
B.5.6 splits the two moved summands, so K fixes the weight-two point in
[Z,L₂]. Its ambient centralizer bound contradicts the original escape of K.

No component, product, decomposition or contradiction certificate remains
as a premise. Local analysis and the strict weak-closure bounds are the
earlier source inputs; their discharge in full 12.3.1 belongs to
qt-d-1231-source. Structural 12.2.2, its genuine seven module alternatives,
and centralizer escape also remain explicit, without a Chapter 13 hypothesis.

Source: Aschbacher–Smith, 12.3.11–13 and completion of 12.3.1,
printed pp.811–812, using the decompositions in 12.3.7, p.809.
The versions in this extension require only `Structural1222At` and
`Theorem1222ModulesAt` at the original G,T. Every overcomponent is treated
in that same ambient group with that same Sylow subgroup. The original
universal declarations and all shared quotient/action records are preserved.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

theorem TerminalPoint.false_of_source_at
    {S : Setup T L V} {D : S.LocalAnalysis} (P : TerminalPoint S D)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (localAnalysis_at : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) : False := by
  obtain ⟨C⟩ := P.componentAnalysis_source_at structural modules escape localAnalysis_at hr hw
  obtain ⟨A⟩ := P.productAnalysis_at structural escape C
  exact P.false_of_module_analysis_at structural A

theorem Setup.false_of_terminal_inputs_at (S : Setup T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (localAnalysis_at : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) : False := by
  obtain ⟨D⟩ := localAnalysis_at L V S
  obtain ⟨P⟩ := exists_terminalPoint_at S D structural escape
  exact P.false_of_source_at structural modules escape localAnalysis_at hr hw

theorem Setup.false_of_uniform_terminal_inputs_at (S : Setup T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (localAnalysis_at : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (rank : ∀ (Y W : Subgroup G), Setup T Y W → (1 : ℕ∞) < ChapterE.globalR W)
    (weakClosure : ∀ (Y W : Subgroup G), Setup T Y W →
      (1 : ℕ∞) < ChapterE.globalW W (T : Subgroup G)) : False :=
  S.false_of_terminal_inputs_at structural modules escape localAnalysis_at
    (rank L V S) (weakClosure L V S)

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven


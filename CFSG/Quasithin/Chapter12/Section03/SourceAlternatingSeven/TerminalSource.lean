module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentSource
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductComplete

/-!+# The terminal A₇ contradiction from the earlier source inputs

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
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The selected point leads to a contradiction after constructing both
intermediate analyses from the original earlier-source assumptions. -/
theorem TerminalPoint.false_of_source
    {S : Setup T L V} {D : S.LocalAnalysis} (P : TerminalPoint S D)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (localAnalysis : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) : False := by
  obtain ⟨C⟩ := P.componentAnalysis_source structural modules escape localAnalysis hr hw
  obtain ⟨A⟩ := P.productAnalysis structural escape C
  exact P.false_of_module_analysis structural A

/-- The terminal conditional contradiction for an original A₇ setup.
Uniform local analysis permits the proper-overcomponent argument, while
the weak-closure bounds are needed only for the original chosen module. -/
theorem Setup.false_of_terminal_inputs (S : Setup T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (localAnalysis : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (hr : (1 : ℕ∞) < ChapterE.globalR V)
    (hw : (1 : ℕ∞) < ChapterE.globalW V (T : Subgroup G)) : False := by
  obtain ⟨D⟩ := localAnalysis L V S
  obtain ⟨P⟩ := exists_terminalPoint S D structural escape
  exact P.false_of_source structural modules escape localAnalysis hr hw

/-- Apply the terminal contradiction to the parent's uniform local-analysis
and weak-closure producers, retaining the original setup and Sylow subgroup. -/
theorem Setup.false_of_uniform_terminal_inputs (S : Setup T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (localAnalysis : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (rank : ∀ (Y W : Subgroup G), Setup T Y W → (1 : ℕ∞) < ChapterE.globalR W)
    (weakClosure : ∀ (Y W : Subgroup G), Setup T Y W →
      (1 : ℕ∞) < ChapterE.globalW W (T : Subgroup G)) : False :=
  S.false_of_terminal_inputs structural modules escape localAnalysis
    (rank L V S) (weakClosure L V S)

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

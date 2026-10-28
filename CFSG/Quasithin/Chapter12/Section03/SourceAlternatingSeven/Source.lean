module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSource
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.WeakClosure
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalSource

/-!
# The A₇ exclusion from the earlier source inputs

Construct the natural action and point-centralizer control on every original
setup. The repaired weak-closure argument then gives r(G,V)>1 and w(G,V)>1,
including the binary simplex case. The terminal component and product theorem
applies to this same setup and yields the contradiction.

Only structural 12.2.2, its seven module alternatives, and uniform centralizer
escape remain explicit. The Chapter13 AlternatingSevenInput adapter derives
escape from Hypothesis 13.1.1 and 12.2.13. Thus this source interface does not
claim the stronger Hypothesis 12.2.3-only theorem without an escape input.
The quotient retains the preimage of Z(L/O₂(L)) under the original projection.

Source: Aschbacher–Smith, Theorem 12.3.1 and its proof, printed pp.807–812.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The original A₇ setup is impossible after constructing the local analysis
and both weak-closure bounds from the authorized earlier-source inputs. -/
theorem Setup.false_of_source (S : Setup T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) : False := by
  have localAnalysis (Y W : Subgroup G) (SY : Setup T Y W) :
      Nonempty SY.LocalAnalysis := SY.localAnalysis_nonempty structural modules escape
  obtain ⟨D⟩ := localAnalysis L V S
  obtain ⟨hr, hw⟩ := weakClosure_bounds S D structural
  exact S.false_of_terminal_inputs structural modules escape localAnalysis hr hw

/-- The literal central quotient of a maximal faithful member cannot be A₇.
Structural 12.2.2 supplies the original chosen module; no local-analysis,
weak-closure, component or product premise remains. -/
theorem centralQuotient_not_alternatingSeven
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    ¬ Nonempty (CentralQuotient L ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  obtain ⟨⟨V, ⟨D⟩⟩⟩ := (structural G T L h).2.1
  exact (Setup.mk h D e).false_of_source structural modules escape

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

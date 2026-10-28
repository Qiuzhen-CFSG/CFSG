module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.Source
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSource
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalSource
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.WeakClosure

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
The versions in this extension require only `Structural1222At` and
`Theorem1222ModulesAt` at the original G,T. Every overcomponent is treated
in that same ambient group with that same Sylow subgroup. The original
universal declarations and all shared quotient/action records are preserved.
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

theorem Setup.false_of_source_at (S : Setup T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) : False := by
  have localAnalysis_at (Y W : Subgroup G) (SY : Setup T Y W) :
      Nonempty SY.LocalAnalysis := SY.localAnalysis_nonempty_at structural modules escape
  obtain ⟨D⟩ := localAnalysis_at L V S
  obtain ⟨hr, hw⟩ := weakClosure_bounds_at S D structural
  exact S.false_of_terminal_inputs_at structural modules escape localAnalysis_at hr hw

theorem centralQuotient_not_alternatingSeven_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    ¬ Nonempty (CentralQuotient L ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  obtain ⟨⟨V, ⟨D⟩⟩⟩ := (structural L h).2.1
  exact (Setup.mk h D e).false_of_source_at structural modules escape

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven


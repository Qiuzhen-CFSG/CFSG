module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.SourceStages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Terminal

/-!
# The common binary critical-pair escape theorem, MS93 (4.3)

For every critical pair (a,a′), V_a escapes Q_c whenever c is exactly two
steps before a′ on a shortest path from a. The only inputs are LocalSource,
Geometry, b > 2, ModuleFacts, and NormalizationTransfer.

The initial constraints, actual commutator pairing, general edge transfer,
and propagation through (4.3.8) construct the preceding source stages.
The final argument constructs a third local conjugate, proves centrality
at six and the radius-six kernel bound, and rules out commutation via a
radius-five normality contradiction. Reversing the resulting critical pair
forces its nonzero commutator into a trivial central intersection.

Both distance branches can use this common result without assuming
CommonFacts or any later source theorem.
Source: Meierfrankenfeld--Stellmacher (1993), printed pp.882–890.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape
open Subgroup Stellmacher.PushingUp.AmalgamGraph
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Original MS93 (4.3), in the binary case: every critical pair escapes the
kernel two steps before its endpoint. All initial, pairing, transfer,
propagation and terminal inputs are discharged from the stated source data. -/
theorem criticalEscape (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R) : CriticalEscape R geometry := by
  obtain ⟨initial, control, edge, propagation, _relative⟩ :=
    SourceStages.sourceStages source geometry hb modules transfer
  intro a ha a' hcritical c hc hpath htrapped
  exact Terminal.counterexample_false source hb modules initial control edge propagation {
    a := a
    a' := a'
    c := c
    color_a := ha
    critical := hcritical
    before := ⟨hc, hpath⟩
    trapped := htrapped
  }

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape

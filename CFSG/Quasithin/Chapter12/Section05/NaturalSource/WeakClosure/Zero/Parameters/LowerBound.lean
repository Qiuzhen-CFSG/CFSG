module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Parameters.Hyperplanes
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Parameters.Setup
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceRecognitionBound
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceSevenEscape

/-!
# The lower exterior corank bound without a Held cover premise

The direct hyperplane calculation rules out the escaping hyperplane supplied
by every A₇ or perfect triple-cover component in E.6.8. This discharges the
literal E.6.18 seven-exclusion input on the original V. The completed E.6.3
source route therefore proves r≥3 and s=3, using the full-automizer value m=3.

The strict inequality r>3 remains separate. The structural input belongs to
qt-d-1222-source and G₃≤M belongs to qt-d-1251-local; no Held center result is
assumed. The literal weak-closure assembly stays with
qt-d-1251-fusion-parameters-zero.

Source: Aschbacher--Smith, E.6.3, E.6.8(4), 12.5.4--6, pp.245,248,819--820.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE ChapterE.Section06
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The actual seven-exclusion input follows from the original G₃ containment. -/
theorem sevenExcluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) :
    Hyperplanes.Enlargement.SevenExcluded s.marking.M V := by
  intro U hU _ J hJ hseven
  obtain ⟨W, hW, _, he⟩ := Components.RemainingSieve.source_sevenEscape
    (s.hypothesisE61 h structural) U hU J hJ hseven
  exact he (inf_le_right.trans (s.marking.centralizer_hyperplane_le hG₃ hW.1 hW.2))

/-- The non-strict r bound and the complete s clause of source 12.5.6. -/
theorem three_le_globalR_and_globalS_eq_three
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hG₃ : s.marking.Gi 3 ≤ s.marking.M) :
    let := D.elementary
    (3 : ℕ∞) ≤ globalR V ∧ globalS V = 3 := by
  let := D.elementary
  have hm := s.localM_eq_three h
  obtain ⟨hr, hs, _⟩ := FrobeniusReduction.lower_bound_knownSimple_of_sevenExcluded
    (s.hypothesisE61 h structural) (by omega : 2 < localM V)
    (s.sevenExcluded h structural hG₃)
  simpa only [hm, Nat.cast_ofNat] using And.intro hr hs

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource

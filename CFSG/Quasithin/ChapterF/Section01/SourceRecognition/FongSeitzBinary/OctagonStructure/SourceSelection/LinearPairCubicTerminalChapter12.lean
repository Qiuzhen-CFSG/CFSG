module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicTerminalInput
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearPairChapter12

/-!
# Chapter 12 consumer for the common cubic terminal input

The selected two-linear row supplies the original factor quotients and the
same marked split quotient used by the source-level `(6G)` calculation.  This
consumer discharges the local `HypothesisF11` and both endpoint model
hypotheses, then packages either degree orientation around
`original_oriented_linear_cubic_terminal_input`.  The nested result retains
the original full Borel and both endpoint maps; no terminal contradiction or
ambient completion recognition is inferred here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.LinearPanel
open ChapterF.Source.FongSeitzBinary.OctagonStructure
open ChapterF.Source.FongSeitzBinary.ReeSource

variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits) (hm : rotationOrder Q = 8)

include D h hmany hn hpsl d hTH e split hm in
/-- The actual selected two-linear source row carries the common cubic actor
and perpendicular product through either quadratic degree orientation. -/
theorem rankOne_octagon_selected_linear_cubic_terminal_input
    (hbranch : ∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
      ((Odd n ∧ b = 2*n) ∨ (Odd b ∧ n = 2*b))) :
    ∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
      ((Odd n ∧ b = 2*n ∧
        original_oriented_linear_cubic_terminal_data
          Q split 0 1 (a := n)) ∨
       (Odd b ∧ n = 2*b ∧
        original_oriented_linear_cubic_terminal_data
          Q split 1 0 (a := b))) := by
  rcases hbranch with ⟨b, hb, hR, hratio⟩
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  rcases hratio with hfirst | hsecond
  · have hbeven : Even b := hfirst.2 ▸ even_two_mul n
    exact ⟨b, hb, hR, Or.inl ⟨hfirst.1, hfirst.2,
      original_oriented_linear_cubic_terminal_input Q e hf split hm
        0 1 (by decide) hfirst.1 hb hbeven
        (by change ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n); exact hpsl)
        (by change ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b); exact hR)⟩⟩
  · have hneven : Even n := hsecond.2 ▸ even_two_mul b
    exact ⟨b, hb, hR, Or.inr ⟨hsecond.1, hsecond.2,
      original_oriented_linear_cubic_terminal_input Q e hf split hm
        1 0 (by decide) hsecond.1 (Nat.zero_lt_of_lt hn) hneven
        (by change ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b); exact hR)
        (by change ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n); exact hpsl)⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

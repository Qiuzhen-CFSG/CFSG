module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonLinearFactor
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Chapter12 hexagon comparison without an opposite-factor assumption

The proper-K/full KnownSimple preparation supplies the original F.1.1
hypotheses and the first linear quotient. The full local catalogue and
mixed exclusions select the opposite linear quotient internally, then
complete the G₂ or triality comparison. The entire original Borel and
both endpoint inclusion squares are retained.

Compared with the earlier linear-hexagon application, no chosen model or
field parameter for R/O₂(R) is required. The marked split quotient,
rotation-six and source square-profile hypotheses remain explicit.
This is the hexagon branch, not the exhaustive seven-row theorem.

Source: Aschbacher–Smith 12.2.2, printed p.795; DGS Theorem D, printed
p.224; Fong–Seitz I (1J), (6C)–(6E), and II §9.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The Chapter12 first linear factor now suffices for hexagon comparison;
the opposite original factor is discharged by the full local catalogue. -/
theorem rankOne_hexagon_comparison_of_square_profile
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 6)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split 0)*Nat.card (simpleRoot Q split 1))) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact HexagonRecognition.marked_hexagon_of_linear_factor Q mark hf split hm 0
    (Nat.zero_lt_of_lt hn) hpsl hsquare

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

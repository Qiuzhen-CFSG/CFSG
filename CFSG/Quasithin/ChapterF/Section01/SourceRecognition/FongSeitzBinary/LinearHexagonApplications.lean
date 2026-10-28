module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearHexagonRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The original Chapter 12 linear hexagon comparison

The proper-K/full KnownSimple preparation supplies F.1.1 for ![L,R]
and its original common Sylow. Its given PSL₂ quotient for L and an
actual PSL₂ quotient for R now give the full G₂ or triality amalgam,
with both original endpoint squares and the entire Borel. There is no
perfectness, field-order relation or local-action premise.

The genuine marked split quotient, rotation order six and selection of
the opposite linear factor retain their earlier source producers. Other
local types and exhaustive seven-row assembly remain separate obligations.
Source: Aschbacher--Smith 12.2.2, p.795; DGS Theorem D, p.224;
Fong--Seitz I (6E), pp.43--45 and II §9.
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

/-- The actual Chapter 12 preparation supplies the first linear factor and
F.1.1. An original linear opposite factor therefore completes the hexagon
comparison without any additional local-action or root-equation hypotheses. -/
theorem rankOne_linear_hexagon_factor_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 6)
    {r : ℕ} (hr : 0 < r)
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^r)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact LinearHexagon.marked_linear_hexagon_of_factor_types Q mark hf split hm
    (Nat.zero_lt_of_lt hn) hr hpsl hR

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

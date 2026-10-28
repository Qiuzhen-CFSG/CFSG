module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.UnequalFactorRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Binary unequal quadrangle recognition for the original Chapter 12 pair

The proper-K/full KnownSimple preparation supplies F.1.1 on the literal
pair ![L,R]. If its marked quotient has rotation order four, both actual
factor quotients are linear and one field is binary and strictly smaller,
the unequal-radical argument forces the other field to have order four.
The resulting full U₄(2) comparison retains both endpoint squares and the
whole overlap, in either orientation. No original endpoint perfectness,
core-structure or quadratic field-ratio premise is added.

Construction of the marked quotient, the split datum, Weyl selection and
the original factor markings remain the earlier source obligations. The
nonbinary unequal and other unmatched rows remain with final assembly.
Source: DGS (11.7), pp.174--175 and Theorem D, p.224; AS 12.2.2 and F.1.1--3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source
open ChapterF.Source.FongSeitzBinary.UnitarySource
variable {G X F k : Type*} [Group G] [Finite G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- A binary smaller original factor and unequal field orders force the
full U₄(2) row, without assuming the quadratic ratio or either core structure. -/
theorem rankOne_unitaryFour_binary_unequal_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (μi : ((![L,R] i) ⧸ pCore 2 (![L,R] i)) ≃* PSL(2,F))
    (μj : ((![L,R] j) ⧸ pCore 2 (![L,R] j)) ≃* PSL(2,k))
    (hlt : Nat.card k < Nat.card F) (hk : Nat.card k = 2) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact marked_binary_unequal_unitaryFour_catalogue Q mark hf split hm i j hij μi μj
    hlt hk

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

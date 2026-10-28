module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.UnequalOrderRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Unequal linear quadrangle recognition for the original Chapter 12 pair

The proper-K/full KnownSimple preparation supplies F.1.1 on the literal
pair ![L,R]. Its two original linear factor quotients and unequal field
orders now force the quadratic ratio: the elementary larger radical
supplies commuting crossed roots, and their Cartan action forces the
smaller binary field degree to divide the larger. The radical order
bound then leaves only the quadratic extension.

The completed U₄ comparison retains both endpoint squares and the whole
Borel in either orientation, for every smaller field, including F₂.
No field-ratio, original core-structure or endpoint-perfectness premise
is required. The earlier source producers retain construction of the
marked split quotient, its rotation order four and the factor markings;
other rows and unconditional seven-row assembly remain to be proved.

Source: DGS (11.6)--(11.7), pp.173--175, and Theorem D, p.224;
Fong--Seitz I (6A)(b), II (8B); AS 12.2.2 and F.1.1--3.
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

/-- Unequal original linear factors force the full U₄ row at every binary
field size, without a field-ratio or core-structure hypothesis. -/
theorem rankOne_unitaryFour_unequal_linear_comparison
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
    (hlt : Nat.card k < Nat.card F) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact marked_unequal_linear_unitaryFour_catalogue Q mark hf split hm i j hij μi μj
    hlt

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

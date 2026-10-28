module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCompleteConsumer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Feeding the original Ree source comparison to Chapter 12

For a selected Chapter 12 preparation, the generic local-pair theorem gives
the literal F.1.1 hypothesis on `![L,R]` and the same source amalgam used by
the global consumer.  The original factor quotient isomorphisms then feed the
completed Section 10 comparison, whose two orientations are packaged as the
actual `ConcreteAmalgamComparison.ree` constructor.

Source: Fong--Seitz I (1973), (6H), pp.51--56; Fong--Seitz II (1974),
Section 10; Aschbacher--Smith, Chapter 12, §2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source
open ChapterF.Source.FongSeitzBinary
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
  (split : SplitData Q.tits) (hm : rotationOrder Q = 8) (m : ℕ)

include D h hmany hn hpsl d hTH e split hm in
/-- The completed original source comparison is a literal Chapter 12 Ree row.

The endpoint inputs are the actual faithful panel quotient isomorphisms.  The
full Borel maps, odd degree and all `(6H)` relations are constructed inside
the source consumer before invoking the final Section 10 comparison.
-/
theorem rankOne_original_factor_ree_comparison
    (μ₀ : ((![L,R] 0) ⧸ pCore 2 (![L,R] 0)) ≃*
      PSL2BinaryMatrixGroup n)
    (μ₁ : ((![L,R] 1) ⧸ pCore 2 (![L,R] 1)) ≃*
      SuzukiMatrixGroup m) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  rcases original_factor_concrete_comparison Q e hf split hm n
    (Nat.zero_lt_of_lt hn) m μ₀ μ₁ with he | he
  · exact Global.ConcreteAmalgamComparison.ree m (Or.inl he)
  · exact Global.ConcreteAmalgamComparison.ree m (Or.inr he)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

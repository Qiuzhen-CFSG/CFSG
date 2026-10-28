module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.Chapter12

/-!
# Removing Chapter 12's two-linear octagon branch

Apply the complete Fong--Seitz (6G) exclusion to the literal original F.1.1
pair. The source-selected Ree branch already gives a full marked amalgam
comparison; the only remaining alternatives here are the two genuine
unitary (6F) branches. The supplied quotient and full amalgam isomorphism
are preserved, including both endpoint squares and the full Borel.

Source: Fong--Seitz I (6G), printed pp.49--51; Aschbacher--Smith 12.2.2.
The unitary exclusions and earlier source quotient construction remain
with the final source assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.OctagonStructure
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits) (hm : rotationOrder Q = 8)
include D h hmany hn d hTH e split hm




/-- The original opposite linear factor is excluded for every positive
degree, including the binary case. -/
theorem rankOne_octagon_linear_pair_false
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b)) : False := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_pair_false Q e hf split hm 0 1 (by decide) (by omega) hb hpsl hR

/-- Close the two-linear branch of the actual marked comparison. Only
the original unitary alternatives remain to be excluded at this boundary. -/
theorem rankOne_octagon_comparison_or_unitary
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)) :
    Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∨
      (∃ b, 0 < b ∧ ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∧
        n % 2 ≠ b % 2 ∧ n ≤ 6*b ∧ 3*b ≤ 2*n) ∨
      (∃ b, 0 < b ∧ IsSU (R ⧸ pCore 2 R) 3 (2^b) ∧
        n % 2 ≠ b % 2 ∧ n ≤ 6*b ∧ 3*b ≤ 2*n) := by
  rcases D.rankOne_octagon_comparison_or_linear_or_unitary h hmany hn hpsl
      d hTH Q e split hm with hcomp | ⟨b,hb,hR,_⟩ | hunitary
  · exact Or.inl hcomp
  · exact (rankOne_octagon_linear_pair_false D h hmany hn d hTH Q e split hm hpsl hb hR).elim
  · exact Or.inr hunitary

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

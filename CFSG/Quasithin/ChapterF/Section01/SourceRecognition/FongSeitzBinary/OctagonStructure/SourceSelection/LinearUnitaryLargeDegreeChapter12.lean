module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearUnitaryLargeDegree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearPairExclusionChapter12

/-!
# Restricting Chapter 12's remaining unitary octagon branches

The original linear/nonbinary-unitary factors now have quadratic field
ratio: the separating-prime fixed radical excludes the larger two ratios.
Apply this to the same Chapter 12 preparation and full marked amalgam
comparison. The remaining alternatives are the quadratic unitary branch
and the explicit small-unitary degrees four and six. Both special and
projective unitary quotients, the full Borel and both endpoint maps remain.

Source: Fong--Seitz I (6F), printed p.46; Aschbacher--Smith 12.2.2.
This is a reduction of the remaining branches, not the final (6F) exclusion.
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

/-- Apply the large-degree exclusion to the literal original factors
of the Chapter 12 preparation. -/
theorem rankOne_octagon_unitary_quadratic_degree
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 2 ≤ b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b)) : Odd b ∧ n=2*b := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_quadratic_degree Q e hf split hm 0 1 (by decide)
    (by omega) hb hpsl hR

/-- The marked comparison now leaves only quadratic unitary parameters
or a degree-one unitary endpoint against linear degree four or six. -/
theorem rankOne_octagon_comparison_or_restricted_unitary
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)) :
    Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∨
      (∃ b, 0 < b ∧ ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∧
        Odd b ∧ (n=2*b ∨ b=1 ∧ (n=4 ∨ n=6))) ∨
      (∃ b, 0 < b ∧ IsSU (R ⧸ pCore 2 R) 3 (2^b) ∧
        Odd b ∧ (n=2*b ∨ b=1 ∧ (n=4 ∨ n=6))) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  have degree {b : ℕ} (hb : 0 < b)
      (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
        IsSU (R ⧸ pCore 2 R) 3 (2^b)) :
      Odd b ∧ (n=2*b ∨ b=1 ∧ (n=4 ∨ n=6)) := by
    by_cases hb1 : b=1
    · obtain ⟨_,ho,hcases⟩ := original_linear_unitary_degrees Q e hf split hm 0 1 (by decide)
        (by omega) hb hpsl hR
      exact ⟨ho,by omega⟩
    · obtain ⟨ho,he⟩ := D.rankOne_octagon_unitary_quadratic_degree h hmany hn d hTH Q e split hm
        hpsl (by omega) hR
      exact ⟨ho,Or.inl he⟩
  rcases D.rankOne_octagon_comparison_or_unitary h hmany hn d hTH Q e split hm hpsl with
    hcomp | ⟨b,hb,hR,_⟩ | ⟨b,hb,hR,_⟩
  · exact Or.inl hcomp
  · exact Or.inr (Or.inl ⟨b,hb,hR,degree hb (Or.inl hR)⟩)
  · exact Or.inr (Or.inr ⟨b,hb,hR,degree hb (Or.inr hR)⟩)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

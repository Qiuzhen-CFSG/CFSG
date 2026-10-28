module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SmallSpecialUnitary
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.SmallProjectiveUnitaryChapter12

/-!
# Chapter 12's remaining unitary octagon alternatives

The original SU3(2) scalar cover now excludes linear degrees four and six.
Thus every unitary alternative in the actual Chapter 12 preparation has
odd unitary degree b and linear degree 2b, for both projective and special
quotients and including degree one. The same original quotient, full Borel
and both endpoint inclusion squares are retained.

Source: Fong--Seitz I (6F), printed p.46; Aschbacher--Smith 12.2.2.
This removes the last larger-degree small-unitary alternatives. The
quadratic-degree contradiction and exhaustive marked recognition remain.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
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

/-- All original unitary degrees in Chapter 12 have quadratic ratio,
including the nonperfect scalar cover SU3(2). -/
theorem rankOne_octagon_unitary_all_quadratic_degree
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b)) : Odd b ∧ n=2*b := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_all_quadratic_degree Q e hf split hm 0 1 (by decide)
    (by omega) hb hpsl hR

/-- At the same marked source quotient, only quadratic unitary alternatives
remain alongside an actual concrete amalgam comparison. -/
theorem rankOne_octagon_comparison_or_quadratic_unitary
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)) :
    Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∨
      (∃ b, 0 < b ∧
        (ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨ IsSU (R ⧸ pCore 2 R) 3 (2^b)) ∧
        Odd b ∧ n=2*b) := by
  rcases D.rankOne_octagon_comparison_or_quadratic_projective_or_special
      h hmany hn d hTH Q e split hm hpsl with hcomp | ⟨b,hb,hR,hdeg⟩ | ⟨b,hb,hR,_⟩
  · exact Or.inl hcomp
  · exact Or.inr ⟨b,hb,Or.inl hR,hdeg⟩
  · exact Or.inr ⟨b,hb,Or.inr hR,
      D.rankOne_octagon_unitary_all_quadratic_degree h hmany hn d hTH Q e split hm hpsl hb (Or.inr hR)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

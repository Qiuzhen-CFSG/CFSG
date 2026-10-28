module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SmallProjectiveUnitary
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearUnitaryLargeDegreeChapter12

/-!
# Chapter 12's projective-unitary octagon has quadratic degree

Apply the small-projective-unitary fixed-radical exclusion to the actual
original factors of the Chapter 12 preparation. Every projective-unitary
alternative now has quadratic field ratio, including unitary degree one.
The special-unitary scalar convention retains its distinct small cases.

The comparison still uses the same quotient, full Borel and both marked
endpoint squares. Source: Fong--Seitz I (6F), printed p.46;
Aschbacher--Smith 12.2.2. The quadratic exclusions and final exhaustive
recognition remain with the source assembly.
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

/-- Every original projective-unitary degree in Chapter 12 has twice its
degree at the linear endpoint, including PSU3(2). -/
theorem rankOne_octagon_projective_unitary_quadratic_degree
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b)) : Odd b ∧ n=2*b := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_projective_unitary_quadratic_degree Q e hf split hm 0 1 (by decide)
    (by omega) hb hpsl hR

/-- Remove the degree-four and degree-six small projective-unitary cases
from the actual marked comparison alternatives. -/
theorem rankOne_octagon_comparison_or_quadratic_projective_or_special
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)) :
    Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∨
      (∃ b, 0 < b ∧ ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∧ Odd b ∧ n=2*b) ∨
      (∃ b, 0 < b ∧ IsSU (R ⧸ pCore 2 R) 3 (2^b) ∧
        Odd b ∧ (n=2*b ∨ b=1 ∧ (n=4 ∨ n=6))) := by
  rcases D.rankOne_octagon_comparison_or_restricted_unitary h hmany hn d hTH Q e split hm hpsl with
    hcomp | ⟨b,hb,hR,_⟩ | hspecial
  · exact Or.inl hcomp
  · exact Or.inr (Or.inl ⟨b,hb,hR,
      D.rankOne_octagon_projective_unitary_quadratic_degree h hmany hn d hTH Q e split hm hpsl hb hR⟩)
  · exact Or.inr (Or.inr hspecial)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

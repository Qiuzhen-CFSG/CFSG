module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryNineEscape
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.UnitaryDerivedChapter12

/-!
# Chapter 12's unitary derived radical escapes the nine-b subgroup

The actual linear/unitary source factors at AS 12.2.2 give the escape of
both the scalar-fixed derived section and the full derived radical from
the nine-b root subgroup. The original quotient and full marked amalgam
supply every local input, including the proved projective section bound.

Source: Fong--Seitz I (6F), printed p.47. The lower-central persistence
argument and terminal source contradiction remain subsequent steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups Pointwise
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

/-- Chapter 12's literal scalar-fixed derived section escapes the nine-b
subgroup, including degree one and both scalar conventions. -/
theorem rankOne_octagon_unitary_scalar_derived_not_le_nine
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b))
    (hK : simpleRemainder Q split 1 ≤ localKernel Q 1) :
    ¬ (unitaryScalarDerivedSection Q split 1 hK).numerator ≤
      unitaryNineSubgroup Q split 0 1 := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_scalar_derived_not_le_nine Q e hf split hm 0 1
    (by decide) (by omega) hb hpsl hR hK

/-- Chapter 12's full derived unitary radical escapes the nine-b subgroup. -/
theorem rankOne_octagon_unitary_derived_not_le_nine
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b)) :
    ¬ ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ ≤
      unitaryNineSubgroup Q split 0 1 := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_derived_not_le_nine Q e hf split hm 0 1
    (by decide) (by omega) hb hpsl hR

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

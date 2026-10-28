module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicSectionSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearPairCubicMiddleChapter12

/-!
# Chapter 12 application of the degree-one middle-root quotients

The selected preparation supplies the original F.1.1 pair and its full
marked amalgam. On that same quotient the middle five-root subgroup has
an elementary quotient of order sixteen. The middle-root centralizer is
parabolic-invariant and has elementary quotient of order one, four or
sixteen. No extra local-action or normality premise is imposed.

Source: Fong--Seitz I (6G), printed p.50. Whole-radical centrality and the
terminal degree-one exclusion are not asserted here.
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


/-- The selected Chapter 12 branch has the actual elementary quotient of
order sixteen by its normal middle five-root subgroup. -/
theorem rankOne_octagon_selected_linear_degree_one_middle_quotient
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2)
    (hn2 : n = 2) :
    ∃ hnormal : ((middleFive Q split 1 0).subgroupOf (simpleRemainder Q split 1)).Normal,
      letI := hnormal
      IsElementaryAbelian 2 ((simpleRemainder Q split 1) ⧸
        (middleFive Q split 1 0).subgroupOf (simpleRemainder Q split 1)) ∧
      Nat.card ((simpleRemainder Q split 1) ⧸
        (middleFive Q split 1 0).subgroupOf (simpleRemainder Q split 1)) = 16 := by
  subst n
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl) hTH
  exact original_linear_degree_one_middle_quotient Q e hf split hm 1 0 (by decide) hR hpsl

/-- On the same marked quotient, the centralizer is normalized by the
entire selected parabolic and has elementary radical quotient of order
one, four or sixteen. Both endpoint maps remain in the source marking. -/
theorem rankOne_octagon_selected_linear_degree_one_centralizer_quotient
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2)
    (hn2 : n = 2) :
    Q.tits.standardParabolic {Q.simple 1} ≤
      normalizer (middleRootCentralizer Q split 1 0 : Set (X ⧸ Q.D)) ∧
    ∃ hnormal : ((middleRootCentralizer Q split 1 0).subgroupOf (simpleRemainder Q split 1)).Normal,
      letI := hnormal
      IsElementaryAbelian 2 ((simpleRemainder Q split 1) ⧸
        (middleRootCentralizer Q split 1 0).subgroupOf (simpleRemainder Q split 1)) ∧
      (Nat.card ((simpleRemainder Q split 1) ⧸
        (middleRootCentralizer Q split 1 0).subgroupOf (simpleRemainder Q split 1)) = 1 ∨
       Nat.card ((simpleRemainder Q split 1) ⧸
        (middleRootCentralizer Q split 1 0).subgroupOf (simpleRemainder Q split 1)) = 4 ∨
       Nat.card ((simpleRemainder Q split 1) ⧸
        (middleRootCentralizer Q split 1 0).subgroupOf (simpleRemainder Q split 1)) = 16) := by
  subst n
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl) hTH
  exact original_linear_degree_one_centralizer_quotient Q e hf split hm 1 0 (by decide) hR hpsl

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

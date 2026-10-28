module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicMiddleSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearPairCubicDegreeOneChapter12

/-!
# Chapter 12 application of the degree-one middle-root centralizer

The selected preparation supplies the genuine F.1.1 pair and both endpoint
maps. The same quotient contains the source's order-128 normal five-root
subgroup and satisfies the centralizer index bound from (6G), printed p.50.
The final degree-one exclusion is not asserted.
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

/-- The original selected branch supplies the normal five-root subgroup
and centralizer index bound on its literal marked quotient. -/
theorem rankOne_octagon_selected_linear_degree_one_middle_centralizer
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2)
    (hn2 : n = 2) :
    Nat.card (middleFive Q split 1 0) = 128 ∧
    middleFive Q split 1 0 ≤ simpleRemainder Q split 1 ⊓
      centralizer (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) : Set (X ⧸ Q.D)) ∧
    simpleRemainder Q split 1 ≤ normalizer (middleFive Q split 1 0 : Set (X ⧸ Q.D)) ∧
    (simpleRemainder Q split 1 ⊓
      centralizer (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) : Set (X ⧸ Q.D))).relIndex
        (simpleRemainder Q split 1) ≤ 16 := by
  subst n
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl) hTH
  exact original_linear_degree_one_middle_centralizer Q e hf split hm
    1 0 (by decide) hR hpsl

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicClosureSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearPairCubicSectionChapter12

/-!
# Chapter 12's actual elementary middle-root normal closure

The selected original F.1.1 pair supplies the degree-one factor markings.
On its same fully marked quotient the middle-root normal closure is elementary,
parabolic-invariant, and central in the five middle roots. The centralizer
quotient acts faithfully on it by conjugation; its nonidentity orbit gives
the order bounds used in the remaining degree-one argument.

Source: Fong--Seitz I (6G), printed p.50. These statements retain the full
Borel and both endpoint maps. They do not assert the terminal exclusion.
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


/-- The selected branch has the actual elementary normal closure and its full-parabolic invariance. -/
theorem rankOne_octagon_selected_linear_degree_one_normal_closure
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2)
    (hn2 : n = 2) :
    IsElementaryAbelian 2 (middleRootClosure Q split 1 0) ∧
    middleRootClosure Q split 1 0 ≤ middleFive Q split 1 0 ⊓
      centralizer (middleFive Q split 1 0 : Set (X ⧸ Q.D)) ∧
    Q.tits.standardParabolic {Q.simple 1} ≤
      normalizer (middleRootClosure Q split 1 0 : Set (X ⧸ Q.D)) ∧
    simpleRemainder Q split 1 ⊓
      centralizer (middleRootClosure Q split 1 0 : Set (X ⧸ Q.D)) =
        middleRootCentralizer Q split 1 0 := by
  subst n
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl) hTH
  exact original_linear_degree_one_normal_closure Q e hf split hm 1 0 (by decide) hR hpsl

/-- The literal radical quotient acts faithfully by conjugation on that normal closure. -/
theorem rankOne_octagon_selected_linear_degree_one_normal_closure_action
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2)
    (hn2 : n = 2) :
    ∃ hn : ((middleRootCentralizer Q split 1 0).subgroupOf
        (simpleRemainder Q split 1)).Normal,
      letI := hn
      ∃ φ : ((simpleRemainder Q split 1) ⧸
          (middleRootCentralizer Q split 1 0).subgroupOf (simpleRemainder Q split 1)) →*
            MulAut (middleRootClosure Q split 1 0),
        Function.Injective φ ∧
        ∀ (v : simpleRemainder Q split 1) (z : middleRootClosure Q split 1 0),
          (φ (QuotientGroup.mk v) z : X ⧸ Q.D) =
            (v : X ⧸ Q.D)*(z : X ⧸ Q.D)*(v : X ⧸ Q.D)⁻¹ := by
  subst n
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl) hTH
  exact original_linear_degree_one_normal_closure_action Q e hf split hm 1 0 (by decide) hR hpsl

/-- The actual conjugacy orbit supplies strict and case-specific order bounds. -/
theorem rankOne_octagon_selected_linear_degree_one_normal_closure_card
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2)
    (hn2 : n = 2) :
    (middleRootCentralizer Q split 1 0).relIndex (simpleRemainder Q split 1) <
      Nat.card (middleRootClosure Q split 1 0) ∧
    Nat.card (middleRootClosure Q split 1 0) ∣ 128 ∧
    ((middleRootCentralizer Q split 1 0).relIndex (simpleRemainder Q split 1) = 4 →
      8 ≤ Nat.card (middleRootClosure Q split 1 0)) ∧
    ((middleRootCentralizer Q split 1 0).relIndex (simpleRemainder Q split 1) = 16 →
      32 ≤ Nat.card (middleRootClosure Q split 1 0)) := by
  subst n
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl) hTH
  exact original_linear_degree_one_normal_closure_card Q e hf split hm 1 0 (by decide) hR hpsl

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairNonbinaryMixed
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearPairCubicExclusionChapter12

/-!
# Chapter 12's higher-degree mixed-root vanishing

Apply the (4B) bound and mixed-root containment to the literal F.1.1
preparation. The quadratic-degree choice supplies the orientation. Both
endpoint maps, the whole Borel and full KnownSimple hypothesis are retained.

Source: Fong--Seitz I (6G), printed p.50, “We claim that”. The subsequent
final commutator contradiction and exhaustive marked comparison remain open.
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




/-- The original linear row supplies the strict derived bound and vanishing
mixed commutator in whichever orientation has odd degree. -/
theorem rankOne_octagon_selected_linear_mixed_commutator
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b)) :
    (Odd n ∧ b = 2*n ∧
      ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ < middleFive Q split 1 0 ∧
      ⁅simpleRoot Q split 1,rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆ = ⊥ ∧
      (rootAt Q split 0 (Q.simple 1*Q.simple 0) ⊔
        rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)) ≤
        centralizer (simpleRemainder Q split 1 : Set (X ⧸ Q.D)) ∧
      ¬ rankOne Q split 1 ≤ normalizer
        ((rootAt Q split 0 (Q.simple 1*Q.simple 0) ⊔
        rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Subgroup (X ⧸ Q.D)) : Set _)) ∨
    (Odd b ∧ n = 2*b ∧
      ⁅simpleRemainder Q split 0,simpleRemainder Q split 0⁆ < middleFive Q split 0 1 ∧
      ⁅simpleRoot Q split 0,rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)⁆ = ⊥ ∧
      (rootAt Q split 1 (Q.simple 0*Q.simple 1) ⊔
        rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) ≤
        centralizer (simpleRemainder Q split 0 : Set (X ⧸ Q.D)) ∧
      ¬ rankOne Q split 0 ≤ normalizer
        ((rootAt Q split 1 (Q.simple 0*Q.simple 1) ⊔
        rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) : Subgroup (X ⧸ Q.D)) : Set _)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_mixed_commutator_alternatives Q e hf split hm 0 1
    (by decide) (by omega) hb hpsl hR

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

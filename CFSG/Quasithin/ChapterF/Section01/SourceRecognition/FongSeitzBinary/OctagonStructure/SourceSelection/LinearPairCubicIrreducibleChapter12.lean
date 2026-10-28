module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicIrreducibleSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearPairCubicDichotomyChapter12

/-!
# Chapter 12's irreducible order-sixteen octagon section

The actual selected PSL₂(4), PSL₂(2) pair supplies the full-Cartan and
rank-one action on the five-root quotient if its middle-root centralizer
is proper. The quotient is elementary abelian of order sixteen, and the
literal conjugation action has no proper nontrivial invariant subgroup.
The same marked quotient, full Borel and both endpoint squares are retained.

Source: Fong--Seitz I (6G), printed p.50, first paragraph. Excluding this
proper-centralizer branch remains with the source recognition argument.
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


/-- The source irreducibility assertion on the same selected quotient,
including its elementary structure, order and conjugation formula. -/
theorem rankOne_octagon_selected_linear_degree_one_proper_centralizer_action
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2)
    (hn2 : n = 2)
    (hproper : middleRootCentralizer Q split 1 0 ≠ simpleRemainder Q split 1) :
    ∃ hn : ((middleFive Q split 1 0).subgroupOf (simpleRemainder Q split 1)).Normal,
      letI := hn
      IsElementaryAbelian 2 ((simpleRemainder Q split 1) ⧸
        (middleFive Q split 1 0).subgroupOf (simpleRemainder Q split 1)) ∧
      Nat.card ((simpleRemainder Q split 1) ⧸
        (middleFive Q split 1 0).subgroupOf (simpleRemainder Q split 1)) = 16 ∧
      ∃ φ : (rankOne Q split 1 ⊔ (Q.tits.B ⊓ Q.tits.N) : Subgroup (X ⧸ Q.D)) →*
          MulAut ((simpleRemainder Q split 1) ⧸
            (middleFive Q split 1 0).subgroupOf (simpleRemainder Q split 1)),
        (∀ (r : (rankOne Q split 1 ⊔ (Q.tits.B ⊓ Q.tits.N) : Subgroup (X ⧸ Q.D)))
          (v : simpleRemainder Q split 1),
          ∃ w : simpleRemainder Q split 1,
            (w : X ⧸ Q.D) = (r : X ⧸ Q.D)*(v : X ⧸ Q.D)*(r : X ⧸ Q.D)⁻¹ ∧
            φ r (QuotientGroup.mk v) = QuotientGroup.mk w) ∧
        ∀ D : Subgroup ((simpleRemainder Q split 1) ⧸
            (middleFive Q split 1 0).subgroupOf (simpleRemainder Q split 1)),
          (∀ r, ∀ x ∈ D, φ r x ∈ D) → D = ⊥ ∨ D = ⊤ := by
  subst n
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl) hTH
  exact original_linear_degree_one_proper_centralizer_action Q e hf split hm 1 0
    (by decide) hR hpsl hproper

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

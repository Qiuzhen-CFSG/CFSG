module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearPairChapter12
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicStructure

/-!
# The cubic structural step at the actual Chapter 12 preparation

The selected two-linear source branch constructs an abelian cubic radical
centralizer of order q³ and commuting perpendicular rank-one groups on the
same quotient. The source theorem uses both original factor marks and the
full amalgam isomorphism, with either degree orientation and no additional
perfectness premise. This is the p.49 structural step of Fong--Seitz I (6G);
its terminal exclusion and exhaustive marked recognition remain separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.LinearPanel
open ChapterF.Source.FongSeitzBinary.OctagonStructure
open ChapterF.Source.FongSeitzBinary.ReeSource

variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits) (hm : rotationOrder Q = 8)

include D h hmany hn hpsl d hTH e split hm in
/-- The original selected linear branch supplies abelian cubic centralizers
and the actual commuting rank-one groups in both orientations. -/
theorem rankOne_octagon_selected_linear_cubic_structure
    (hbranch : ∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
      ((Odd n ∧ b = 2*n) ∨ (Odd b ∧ n = 2*b))) :
    ∃ b, 0 < b ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b) ∧
      ((Odd n ∧ b = 2*n ∧
        ∃ c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
          orderOf c = 3 ∧
          IsMulCommutative ↥(simpleRemainder Q split 0 ⊓
            centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D))) ∧
          Nat.card (simpleRemainder Q split 0 ⊓
            centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = (2^n)^3 ∧
          ⁅rankOne Q split 0,rightConjugate (rankOne Q split 0)
            (representative (Q.simple 1*Q.simple 0*Q.simple 1) : X ⧸ Q.D)⁆ = ⊥) ∨
       (Odd b ∧ n = 2*b ∧
        ∃ c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)),
          orderOf c = 3 ∧
          IsMulCommutative ↥(simpleRemainder Q split 1 ⊓
            centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D))) ∧
          Nat.card (simpleRemainder Q split 1 ⊓
            centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = (2^b)^3 ∧
          ⁅rankOne Q split 1,rightConjugate (rankOne Q split 1)
            (representative (Q.simple 0*Q.simple 1*Q.simple 0) : X ⧸ Q.D)⁆ = ⊥)) := by
  rcases hbranch with ⟨b,hb,hR,_⟩
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact ⟨b,hb,hR,original_linear_pair_cubic_structure Q e hf split hm 0 1 (by decide)
    (a := n) (b := b) (by omega) hb hpsl hR⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

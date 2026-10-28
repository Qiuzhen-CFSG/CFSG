module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryNineSubgroup
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.UnitaryDerivedChapter12

/-!
# Chapter 12's literal nine-degree unitary subgroup

Apply the original-factor construction to the same marked quotient and
full source amalgam. The resulting X has order 2^(9b); its commutator
contains the middle Frattini root of order 2^b, and the entire cubic
fixed radical lies in X. Both SU3 and PSU3 conventions and b=1 are kept.

Source: Fong--Seitz I (6F), printed p.47, at the AS 12.2.2 consumer.
This supplies the actual subgroup used in the exclusion argument, not
the projective-action exclusion or final marked recognition.
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
  (split : SplitData Q.tits) (hm : rotationOrder Q=8)
include D h hmany hn d hTH e split hm

/-- Chapter 12's actual original factors give the source's subgroup X
and its middle Frattini commutator, without any new representation premise. -/
theorem rankOne_octagon_unitary_nine_subgroup
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b)) :
    let X₉ := unitaryNineSubgroup Q split 0 1
    let C := rootFrattiniAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
    Nat.card X₉=2^(9*b) ∧ Nat.card C=2^b ∧ C ≤ ⁅X₉,X₉⁆ ∧
      simpleRemainder Q split 1 ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ≤ X₉ := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_nine_subgroup Q e hf split hm 0 1 (by decide)
    (by omega) hb hpsl hR

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

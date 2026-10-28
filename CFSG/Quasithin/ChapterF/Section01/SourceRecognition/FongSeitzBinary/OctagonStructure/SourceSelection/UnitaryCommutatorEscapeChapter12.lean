module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryCommutatorEscape
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.UnitaryDerivedChapter12

/-!
# Chapter 12's next unitary lower-central term

The original source factors at AS 12.2.2 supply the six-b Frattini bound
and nontrivial unitary action on the actual third lower-central term.
The derived-radical escape is discharged by the established nine-b
exclusion. A general escaping-subgroup version supplies the same step for
later terms on the unchanged quotient and full marked amalgam.

Source: Fong--Seitz I (6F), printed p.47. The stronger projective-section
persistence and final source contradiction remain subsequent arguments.
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

/-- The next commutator of a literal escaping invariant subgroup has the
source six-b Frattini bound, including the degree-one unitary actors. -/
theorem rankOne_octagon_unitary_next_commutator
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b))
    (W : Subgroup (X ⧸ Q.D)) (hWM : W ≤ middleFive Q split 1 0)
    (hWR : rankOne Q split 1 ≤ normalizer (W : Set (X ⧸ Q.D)))
    (hescape : ¬ W ≤ unitaryNineSubgroup Q split 0 1) :
    let C := ⁅W,simpleRemainder Q split 1⁆
    ⁅rankOne Q split 1,C⁆ ≠ ⊥ ∧ 2^(6*b) ≤ Nat.card (C ⧸ frattini C) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_next_commutator Q e hf split hm 0 1
    (by decide) (by omega) hb hpsl hR W hWM hWR hescape

/-- The actual third lower-central term of Chapter 12's unitary radical
has nontrivial unitary action and the six-b Frattini bound. -/
theorem rankOne_octagon_unitary_triple_commutator
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b)) :
    let U := simpleRemainder Q split 1
    let C := ⁅⁅U,U⁆,U⁆
    ⁅rankOne Q split 1,C⁆ ≠ ⊥ ∧ 2^(6*b) ≤ Nat.card (C ⧸ frattini C) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_triple_commutator Q e hf split hm 0 1
    (by decide) (by omega) hb hpsl hR

/-- Chapter 12's original derived quotient by the third lower-central
term has order at most 2^(7b). -/
theorem rankOne_octagon_unitary_derived_mod_triple_bound
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b)) :
    let U := simpleRemainder Q split 1
    let C := ⁅U,U⁆
    Nat.card (C ⧸ (⁅C,U⁆).subgroupOf C) ≤ 2^(7*b) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_derived_mod_triple_bound Q e hf split hm 0 1
    (by decide) (by omega) hb hpsl hR

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

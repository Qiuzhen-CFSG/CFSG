module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryNineCenter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.UnitaryNineSubgroupChapter12

/-!
# Chapter 12's unitary middle-root center obstruction

The literal original factor alternative excludes simultaneous containment of
X' and Z(X) in the middle Frattini root of X. The cubic fixed subgroup and
its nontrivial outer roots are constructed from the source; no new action
or center hypothesis is imposed. The strict-center form is also exposed
for the subsequent invariant-subgroup argument. Full Borel, both endpoint
squares, the original quotient and both SU3/PSU3 conventions remain intact.

Source: Fong--Seitz I (6F), printed p.47, at the AS 12.2.2 consumer.
The projective degree bound, invariant-subgroup reduction and lower-central
persistence are still required before the exhaustive marked comparison.
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

/-- The original Chapter 12 factors force a strictly larger center if X'
is contained in the middle Frattini root. -/
theorem rankOne_octagon_unitary_nine_center_gt_middle
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b)) :
    let X₉ := unitaryNineSubgroup Q split 0 1
    let M := rootFrattiniAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
    ⁅X₉,X₉⁆ ≤ M → M < (center X₉).map X₉.subtype := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_nine_center_gt_middle Q e hf split hm 0 1 (by decide)
    (by omega) hb hpsl hR

/-- The actual middle root cannot simultaneously contain the derived subgroup
and embedded center of the source X, including unitary degree one. -/
theorem rankOne_octagon_unitary_nine_not_special_middle
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b)) :
    let X₉ := unitaryNineSubgroup Q split 0 1
    let M := rootFrattiniAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
    ¬ (⁅X₉,X₉⁆ ≤ M ∧ (center X₉).map X₉.subtype ≤ M) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_nine_not_special_middle Q e hf split hm 0 1 (by decide)
    (by omega) hb hpsl hR

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryNineCenter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryNineSubgroup

/-!
# The original unitary factors exclude the middle-root center of X

The genuine original PSL2 and SU3/PSU3 markings give a nontrivial middle
Frattini root, the full cubic fixed radical and its abelianness. If the
source subgroup X has derived subgroup inside that middle root, coprime
centrality puts all three fixed Frattini roots in its center. The center
therefore strictly contains the middle root. This excludes the simultaneous
derived and center equalities used in the source's invariant-subgroup argument.

Both orientations, scalar conventions and degree one are retained, together
with the same quotient, full Borel and both endpoint inclusion squares.
Source: Fong--Seitz I (6F), printed p.47. The reduction of an invariant
subgroup to these equalities and lower-central persistence remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1)
      inf_le_left inf_le_right) Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
include e h split

/-- The actual center strictly exceeds the middle root whenever X' lies in it.
Every cubic-action and root-size input is supplied by the original factors. -/
theorem original_linear_unitary_nine_center_gt_middle
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    let X₉ := unitaryNineSubgroup Q split i j
    let M := rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)
    ⁅X₉,X₉⁆ ≤ M → M < (center X₉).map X₉.subtype := by
  dsimp only
  intro hder
  have hfixed := (original_linear_unitary_cubic_fixed_roots Q e h split hm i j hij ha hb hi hj).2
  have hnine := original_linear_unitary_nine_subgroup Q e h split hm i j hij ha hb hi hj
  have hab := original_linear_unitary_cubic_radical_abelian Q e h split hm i j hij ha hb hi hj
  apply unitaryNineSubgroup_center_gt_middle_of_derived_le Q split hm i j hij
    hnine.2.2.2 hab (fun w => (hfixed w).2.1) ?_ hder
  rw [hnine.2.1]
  exact Nat.one_lt_pow (by omega) (by decide)

/-- The two middle-root equalities in the source cannot hold for the actual X.
This is the terminal center obstruction, with no extra structural premise. -/
theorem original_linear_unitary_nine_not_special_middle
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^a))
    (hj : ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b) ∨
      IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^b)) :
    let X₉ := unitaryNineSubgroup Q split i j
    let M := rootFrattiniAt Q split j (Q.simple i*Q.simple j*Q.simple i)
    ¬ (⁅X₉,X₉⁆ ≤ M ∧ (center X₉).map X₉.subtype ≤ M) := by
  dsimp only
  rintro ⟨hder,hcenter⟩
  exact (not_le_of_gt (original_linear_unitary_nine_center_gt_middle
    Q e h split hm i j hij ha hb hi hj hder)) hcenter

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure

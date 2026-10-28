module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryNineIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.UnitaryNineSubgroupChapter12

/-!
# Chapter 12's middle-root intersection and subgroup bounds

The literal source factors give the three full-Cartan invariant subgroups
of the middle unitary root, the 2^(7b) bounds for small intersections,
elementary abelian subgroups and the center of X, and the whole middle-root
containment for larger Cartan-invariant subgroups. Degree one and both
special/projective scalar conventions are included. The original quotient,
full Borel and both endpoint squares remain the same.

Source: Fong--Seitz I (6F), printed p.47, applied at AS 12.2.2.
The projective degree gap and the remaining invariant-subgroup and
lower-central arguments are still needed for full recognition.
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

/-- All intersection and size assertions at the actual Chapter 12 factors. -/
theorem rankOne_octagon_unitary_nine_subgroup_control
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b)) :
    let K := unitaryNineSubgroup Q split 0 1
    let C := rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
    let M := rootFrattiniAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)
    Nat.card (center K) ≤ 2^(7*b) ∧
      (∀ W : Subgroup (X ⧸ Q.D), W ≤ K → C ⊓ W ≤ M → Nat.card W ≤ 2^(7*b)) ∧
      (∀ W : Subgroup (X ⧸ Q.D), W ≤ K → IsElementaryAbelian 2 W → Nat.card W ≤ 2^(7*b)) ∧
      (∀ W : Subgroup (X ⧸ Q.D), W ≤ C →
        Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D)) → W=⊥ ∨ W=M ∨ W=C) ∧
      (∀ W : Subgroup (X ⧸ Q.D), W ≤ K →
        Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D)) →
        2^(7*b) < Nat.card W → C ≤ W) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_nine_subgroup_control Q e hf split hm 0 1 (by decide)
    (by omega) hb hpsl hR

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

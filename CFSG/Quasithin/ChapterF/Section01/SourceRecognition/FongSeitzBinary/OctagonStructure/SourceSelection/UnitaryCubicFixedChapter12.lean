module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryCubicFixed
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.SmallSpecialUnitaryChapter12

/-!
# Chapter 12's actual cubic root centralizers

For every surviving unitary octagon alternative, the three-core of the
same full Cartan is nontrivial. It fixes exactly each unitary root Frattini subgroup, equal to its center,
and no nonidentity point of any linear root. The original special and
projective quotient conventions, including degree one and its scalar
cover, are preserved through the actual marked amalgam.

Source: Fong--Seitz I (6F), printed pp.46--47; AS 12.2.2.
The radical centralizer and terminal unitary exclusion remain required.
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

/-- The literal Chapter 12 source supplies both complete cubic fixed-root
identities, including its nonperfect binary unitary alternative. -/
theorem rankOne_octagon_unitary_cubic_fixed_roots
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b)) :
    cartanThreeCore Q ≠ ⊥ ∧ ∀ w : Weyl Q,
      (rootAt Q split 0 w ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) = ⊥) ∧
      rootAt Q split 1 w ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) =
        (frattini (rootAt Q split 1 w)).map (rootAt Q split 1 w).subtype ∧
      frattini (rootAt Q split 1 w) = center (rootAt Q split 1 w) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_cubic_fixed_roots Q e hf split hm 0 1 (by decide)
    (by omega) hb hpsl hR

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

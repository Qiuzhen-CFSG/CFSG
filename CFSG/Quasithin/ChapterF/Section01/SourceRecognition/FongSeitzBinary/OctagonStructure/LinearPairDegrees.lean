module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.LinearPairCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.LinearActions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCartan
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorLevi

/-!
# Original-source degree reduction for the linear octagon pair

The actual full Borel markings give elementary abelian roots of the two
binary field orders. The octagon square theorem orients one degree as odd
and the other as even. The perpendicular-root Cartan argument then makes
the odd degree divide the even one. Both original quotient maps are
transported through the supplied F.1.1 amalgam isomorphism; the Borel-core
and reflection premises are discharged on that same quotient.

This is the initial reduction in Fong--Seitz I (6G), printed p.49.
The numerical (1K) bound and the subsequent root centralizer contradiction
remain separate steps. In particular the possible degrees one and two
are retained rather than discarded by a simplicity assumption.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure
open ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
  (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
  (μi : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL2BinaryMatrixGroup a)
  (Ti : Sylow 2 (PSL2BinaryMatrixGroup a))
  (hBi : (quotientBorel Q i).map μi.toMonoidHom = normalizer (Ti : Set _))
  (μj : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup b)
  (Tj : Sylow 2 (PSL2BinaryMatrixGroup b))
  (hBj : (quotientBorel Q j).map μj.toMonoidHom = normalizer (Tj : Set _))
  (hcore : Q.tits.B.normalCore = ⊥)

include split hm hij ha hb μi hBi μj hBj hcore in
/-- The two original full linear panels orient the odd degree, with divisibility proved. -/
theorem linear_pair_oriented_degrees :
    (Odd a ∧ Even b ∧ a ∣ b) ∨ (Even a ∧ Odd b ∧ b ∣ a) := by
  have hci : Nat.card (simpleRoot Q split i) = 2^a := by
    simpa only [HexagonStructure.rootAt_one] using linear_rootAt_card Q split i a μi Ti hBi ha 1
  have hcj : Nat.card (simpleRoot Q split j) = 2^b := by
    simpa only [HexagonStructure.rootAt_one] using linear_rootAt_card Q split j b μj Tj hBj hb 1
  have hei : IsElementaryAbelian 2 (simpleRoot Q split i) := by
    rw [← HexagonStructure.rootAt_one Q split i]
    exact linear_rootAt_elementary Q split i a μi Ti hBi 1
  have hej : IsElementaryAbelian 2 (simpleRoot Q split j) := by
    rw [← HexagonStructure.rootAt_one Q split j]
    exact linear_rootAt_elementary Q split j b μj Tj hBj 1
  obtain ⟨hoa,heb⟩ | ⟨hea,hob⟩ := linear_pair_degree_parity Q split hm i j hij hci hcj
  · exact Or.inl ⟨hoa,heb,linear_pair_odd_degree_dvd Q split hm i j hij a b hoa hb
      μi Ti hBi μj Tj hBj hei hci (UnitarySource.actorReflection Q split) hcore⟩
  · exact Or.inr ⟨hea,hob,linear_pair_odd_degree_dvd Q split hm j i hij.symm b a hob ha
      μj Tj hBj μi Ti hBi hej hcj (UnitarySource.actorReflection Q split) hcore⟩

open MarkedLocal
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

include Q split hm hij ha hb in
/-- F.1.1 quotient transport discharges the full Borel, reflection and core premises. -/
theorem original_linear_pair_oriented_degrees
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S)
    (νi : (parabolic L S i ⧸ originalPanelKernel (L := L) (S := S) i) ≃*
      PSL2BinaryMatrixGroup a)
    (Ui : Sylow 2 (PSL2BinaryMatrixGroup a))
    (hCi : (originalFaithfulBorel (L := L) (S := S) i).map νi.toMonoidHom =
      normalizer (Ui : Set _))
    (νj : (parabolic L S j ⧸ originalPanelKernel (L := L) (S := S) j) ≃*
      PSL2BinaryMatrixGroup b)
    (Uj : Sylow 2 (PSL2BinaryMatrixGroup b))
    (hCj : (originalFaithfulBorel (L := L) (S := S) j).map νj.toMonoidHom =
      normalizer (Uj : Set _)) :
    (Odd a ∧ Even b ∧ a ∣ b) ∨ (Even a ∧ Odd b ∧ b ∣ a) :=
  linear_pair_oriented_degrees Q split hm i j hij a b ha hb
    (faithfulModelMarking Q e h i νi) Ui (faithfulModelMarking_borel Q e h i νi _ hCi)
    (faithfulModelMarking Q e h j νj) Uj (faithfulModelMarking_borel Q e h j νj _ hCj)
    (LinearThreePresentation.borel_core_eq_bot Q e h)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.OctagonStructure

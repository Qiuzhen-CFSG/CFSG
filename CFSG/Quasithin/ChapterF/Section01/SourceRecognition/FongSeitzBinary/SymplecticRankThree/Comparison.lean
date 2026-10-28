module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.Markings
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.Counts
public import Theory.GroupAction.SymplecticRankThree.IncidenceAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.Source
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.SymplecticFour

/-!
# Original C₂ incidence and comparison applications

The actual original/geometric endpoint marking supplies local
characteristic two on the same quotient. Its coset action therefore gives
projective incidence axioms from the source subdegrees and root fixation.
Separately, a normal symplectic subgroup of the correct field size is the
whole quotient; the Sylow-normalized marking then gives the full model
amalgam in either orientation, retaining both inclusion squares.

These two applications expose the remaining gap precisely: projective
coordinatization and elation generation must construct the normal
symplectic subgroup. The source coset counts and root fixation are also
still explicit; neither theorem is the original source recognition.

Source: Fong–Seitz II (7C), p.193 and (8A), p.197; Higman (1964),
Lemma 10 and Theorem 2(i), pp.153–155; Aschbacher–Smith F.1.1–12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.SpecificGroups.SymplecticFour
open Theory.GroupAction.SymplecticRankThree
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
/-- The source cosets satisfy Veblen and have four noncoplanar points once
their literal subdegrees and root fixation are proved. -/
theorem marked_projective_incidence
    {q : ℕ} (hq : 2 ≤ q)
    (b c : C2RankThree.Points Q 1) (hab : C2RankThree.rightCosetPoint Q 1 1 ≠ b)
    (t : X ⧸ Q.D) (hta : t • C2RankThree.rightCosetPoint Q 1 1 = b)
    (htb : t • b = C2RankThree.rightCosetPoint Q 1 1)
    (hcov : MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (C2RankThree.rightCosetPoint Q 1 1)) c =
      (insert (C2RankThree.rightCosetPoint Q 1 1)
        (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (C2RankThree.rightCosetPoint Q 1 1)) b))ᶜ)
    (hm : rotationOrder Q = 4)
    (hq0 : Nat.card (simpleRoot Q split 0) = q)
    (hsubdegree : Nat.card
      (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (C2RankThree.rightCosetPoint Q 1 1)) b) = q*(q+1))
    (hq1 : Nat.card (simpleRoot Q split 1) = q)
    (hfix : ∀ u ∈ C2RankThree.kernelRoot Q split,
      ∀ c ∈ insert (C2RankThree.rightCosetPoint Q 1 1)
        (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (C2RankThree.rightCosetPoint Q 1 1)) b), u • c = c) :
    ∃ D : PolarityDesign (C2RankThree.Points Q 1) q,
      (∀ x y, D.incident x y ↔ y = x ∨
        (MulAction.SwappedOrbital.graph (C2RankThree.rightCosetPoint Q 1 1) b hab t hta htb).Adj x y) ∧
      D.block (C2RankThree.rightCosetPoint Q 1 1) = insert (C2RankThree.rightCosetPoint Q 1 1)
        (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (C2RankThree.rightCosetPoint Q 1 1)) b) ∧
      (∀ x y, x ≠ y → (D.line x y).ncard = q+1) ∧
      (∀ x y p, x ≠ y → (D.line x y ∩ D.block p).Nonempty) ∧
      (∀ x y z, x ≠ y → z ∉ D.line x y →
        ∃! p, x ∈ D.block p ∧ y ∈ D.block p ∧ z ∈ D.block p) ∧
      (∀ x y z w, z ≠ w → x ≠ z → y ≠ w →
        (D.line x y ∩ D.line z w).Nonempty → (D.line x z ∩ D.line y w).Nonempty) ∧
      (∃ x y z w, x ≠ y ∧ z ∉ D.line x y ∧
        ¬ ∃ p, x ∈ D.block p ∧ y ∈ D.block p ∧ z ∈ D.block p ∧ w ∈ D.block p) := by
  let := marked_coset_faithful Q e h split 1
  let := C2RankThree.primitive Q 1
  let := Fintype.ofFinite (C2RankThree.Points Q 1)
  exact condition_i_incidence hq (C2RankThree.rightCosetPoint Q 1 1) b c hab t hta htb
    hcov (C2RankThree.points_card Q split hm hq0 hq1 1) hsubdegree
    (C2RankThree.kernel_lower_bound Q split _ hq1 hfix)

include e h in
/-- A recognized normal symplectic subgroup gives both full endpoint markings.
Its existence is the undischarged geometric recognition obligation. -/
theorem comparison_of_normal_symplectic
    (hm : rotationOrder Q = 4)
    (hq0 : Nat.card (simpleRoot Q split 0) = Nat.card F)
    (hq1 : Nat.card (simpleRoot Q split 1) = Nat.card F)
    (hgen : split.unipotentClosure = ⊤)
    (K : Subgroup (X ⧸ Q.D)) [K.Normal] (model : K ≃* Sp F) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (GreenBook.LieModels.SymplecticFour.amalgam F).reverse) := by
  let E := C2RankThree.wholeEquiv Q split hgen
    (C2RankThree.unipotent_card Q split hm hq0 hq1) K model
  rcases C2RankThree.marked_comparison_of_equiv Q split
    (MarkedLocal.parabolic_core_selfCentralizing Q e h) E with hf | hf
  · obtain ⟨f⟩ := hf
    exact Or.inl ⟨e.trans f⟩
  · obtain ⟨f⟩ := hf
    exact Or.inr ⟨e.trans f⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree

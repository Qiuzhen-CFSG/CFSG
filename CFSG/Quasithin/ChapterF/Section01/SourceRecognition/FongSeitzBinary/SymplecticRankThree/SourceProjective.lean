module
public import Theory.GroupAction.SymplecticRankThree.AlternatingPolarity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.SourceCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.BinaryComparison
public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport

/-!
# Source C₂ comparison from ordinary projective coordinates

The original local PSL₂ markings and selected (6A)(a) row supply the
polarity design on the literal second-parabolic cosets. Ordinary line
coordinates transport its blocks to hyperplanes. The proved null-polarity
realization then constructs a compatible alternating form and polar
coordinates, discharging the former orthogonality premise. Elation generation
and root-normal-generation yield full Sp₄, and the saved marking construction
recovers the full Borel and both endpoint squares in either orientation.

At q=2 the complete binary theorem is used directly, followed by field
transport of the full Sp₄(2); no coordinate premise is required there.
For q>2 ordinary projective coordinates remain to be constructed from incidence.
This module does not claim to discharge that remaining source obligation.

Source: Higman (1964), Lemma 10 and Theorem 2(i), pp.153–155;
Fong–Seitz I (6A)(a), II (7C) and (8A); Aschbacher–Smith F.1.1–12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.GroupAction.SymplecticRankThree
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
local notation "a" => C2RankThree.rightCosetPoint Q 1 1
local notation "b" => C2RankThree.neighborPoint Q
local notation "Γ" => MulAction.SwappedOrbital.graph a b (C2RankThree.base_ne_neighbor Q)
  (representative (Q.simple 0) : X ⧸ Q.D)⁻¹
  (C2RankThree.neighbor_swap_base Q) (C2RankThree.neighbor_swap_neighbor Q)

/-- The projective line defined from closed neighbor blocks on the actual
parabolic cosets. This definition supplies no coordinate structure. -/
@[expose] def orbitalLine (x y : C2RankThree.Points Q 1) : Set (C2RankThree.Points Q 1) :=
  {z | ∀ w, (x = w ∨ (Γ).Adj w x) → (y = w ∨ (Γ).Adj w y) →
    (z = w ∨ (Γ).Adj w z)}

variable (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
/-- Construct the polar coordinates of the same quotient from ordinary line
coordinates; the alternating-pairing premise is discharged. -/
theorem source_polar_coordinates_of_projective_coordinates
    (hF : Nat.card F ≠ 2)
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥)
    (C : C2RankThree.Points Q 1 ≃ ProjectivePoint F)
    (hC : ∀ x y z, (C z).submodule ≤ (C x).submodule ⊔ (C y).submodule ↔
      z ∈ orbitalLine Q x y) :
    ∃ E : C2RankThree.Points Q 1 ≃ ProjectivePoint F,
      ∀ x y, Orthogonal (E x) (E y) ↔ y = x ∨ (Γ).Adj x y := by
  obtain ⟨D,hD,_⟩ := marked_projective_incidence_of_linear_row Q e h split hm μ hq hrow
  have hl : ∀ x y z, (C z).submodule ≤ (C x).submodule ⊔ (C y).submodule ↔ z ∈ D.line x y := by
    intro x y z
    rw [hC]
    simp only [PolarityDesign.mem_line,hD,orbitalLine,Set.mem_ofPred_eq]
  obtain ⟨E,hE⟩ := D.polar_coordinates_of_line_coordinates hF C hl
  exact ⟨E,fun x y => (hE x y).trans (hD x y)⟩

include e h in
/-- Both marked endpoints and the full Borel, with ordinary coordinates only
in the nonbinary branch. Full Sp₄(2) uses the proved binary recognition. -/
theorem comparison_of_projective_coordinates
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥)
    (hgen : split.unipotentClosure = ⊤)
    (coordinates : Nat.card F ≠ 2 → ∃ C : C2RankThree.Points Q 1 ≃ ProjectivePoint F,
      ∀ x y z, (C z).submodule ≤ (C x).submodule ⊔ (C y).submodule ↔
        z ∈ orbitalLine Q x y) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (GreenBook.LieModels.SymplecticFour.amalgam F).reverse) := by
  by_cases hF : Nat.card F = 2
  · have hc := MarkedLocal.parabolic_core_selfCentralizing Q e h
    obtain ⟨E⟩ := C2RankThree.binary_symplectic_equiv Q split (hc 1) hm
      (fun i => (hq i).trans hF) hrow
    let E' : (X ⧸ Q.D) ≃* Sp F := E.trans
      (Binary.fieldEquivSp (Binary.fieldEquivZModTwo F hF).symm)
    rcases C2RankThree.marked_comparison_of_equiv Q split hc E' with hf | hf
    · exact Or.inl ⟨e.trans hf.some⟩
    · exact Or.inr ⟨e.trans hf.some⟩
  · obtain ⟨C,hC⟩ := coordinates hF
    obtain ⟨E,hE⟩ := source_polar_coordinates_of_projective_coordinates Q e h split hF hm μ hq hrow C hC
    exact comparison_of_polar_coordinates Q e h split hm μ hq hrow hgen E hE

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree

module
public import Theory.GroupAction.SymplecticRankThree.Higman
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.SourceProjective

/-!
# Recognition of the original C₂ row by rank-three geometry

The selected (6A)(a) row and the genuine paired local PSL₂ quotients give the
actual coset geometry and its kernel bound. Spatial coordinatization now supplies
one projective chart over that same local field. The proved null-polarity and
elation arguments construct a normal full Sp₄ subgroup; unipotent normal
generation makes it the entire quotient. At order two the independent binary
proof constructs full Sp₄(2), followed by field transport.

Sylow alignment recovers the full Borel and both parabolics in either permitted
orientation. The existing marking adapter restricts one quotient equivalence,
retaining both commuting squares and the literal Q.q. No coordinates, model
homomorphism, source simplicity or recognition callback remain as inputs.
The row, local quotient markings and root-normal-generation are the earlier
source producers owned by the split-quotient and source-assembly tasks.

Source: Fong–Seitz I (6A)(a), II (7C), p.193 and (8A), p.197;
Higman (1964), Lemma 10 and Theorem 2(i), pp.153–155.
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
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
/-- Construct all projective coordinates on the same nonbinary source quotient. -/
theorem projective_coordinates_of_linear_row
    (hF : Nat.card F ≠ 2)
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥) :
    ∃ C : C2RankThree.Points Q 1 ≃ ProjectivePoint F,
      ∀ x y z, (C z).submodule ≤ (C x).submodule ⊔ (C y).submodule ↔
        z ∈ orbitalLine Q x y := by
  obtain ⟨D,hD,_,hl,_⟩ := marked_projective_incidence_of_linear_row Q e h split hm μ hq hrow
  have hL (x y : C2RankThree.Points Q 1) : D.line x y = orbitalLine Q x y := by
    ext z
    simp only [PolarityDesign.mem_line,hD,orbitalLine,Set.mem_ofPred_eq]
  have hq' : 2 ≤ Nat.card F := by have := Finite.one_lt_card (α := F); omega
  obtain ⟨f,_⟩ := D.exists_affineFrame hl hq'
    (C2RankThree.points_card Q split hm (hq 0) (hq 1) 1) (C2RankThree.rightCosetPoint Q 1 1)
  obtain ⟨C,hC⟩ := f.exists_projective_space_coordinates hl hq' F rfl hF
  exact ⟨C,fun x y z => (hC x y z).trans (by rw [hL])⟩

include e h in
/-- The actual C₂ quotient contains a normal full symplectic subgroup.
This includes full Sp₄(2); no source simplicity is used. -/
theorem normal_symplectic_of_linear_row
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥) :
    ∃ K : Subgroup (X ⧸ Q.D), K.Normal ∧ Nonempty (K ≃* Sp F) := by
  let := marked_coset_faithful Q e h split 1
  let := C2RankThree.primitive Q 1
  let := Fintype.ofFinite (C2RankThree.Points Q 1)
  have hfix := C2RankThree.kernelRoot_fixes_of_central Q split hm
    (linear_kernelRoot_central Q split hm μ hq hrow)
  exact condition_i_recognition (F := F)
    (C2RankThree.rightCosetPoint Q 1 1) (C2RankThree.neighborPoint Q) (C2RankThree.oppositePoint Q)
    (C2RankThree.base_ne_neighbor Q) (representative (Q.simple 0) : X ⧸ Q.D)⁻¹
    (C2RankThree.neighbor_swap_base Q) (C2RankThree.neighbor_swap_neighbor Q)
    (C2RankThree.opposite_orbit_eq_compl Q hm)
    (C2RankThree.points_card Q split hm (hq 0) (hq 1) 1)
    (C2RankThree.neighbor_orbit_card Q split hm (hq 0) (hq 1))
    (C2RankThree.kernel_lower_bound Q split _ (hq 1) hfix)

include e h in
/-- Full Sylow order and root-normal-generation identify the entire quotient. -/
theorem symplectic_equiv_of_linear_row
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥)
    (hgen : split.unipotentClosure = ⊤) : Nonempty ((X ⧸ Q.D) ≃* Sp F) := by
  obtain ⟨K,hK,⟨E⟩⟩ := normal_symplectic_of_linear_row Q e h split hm μ hq hrow
  let := hK
  exact ⟨C2RankThree.wholeEquiv Q split hgen
    (C2RankThree.unipotent_card Q split hm (hq 0) (hq 1)) K E⟩

include e h in
/-- One adjusted equivalence simultaneously maps U, the full Borel and both
marked endpoints, with precisely the two permitted orientations. -/
theorem aligned_symplectic_equiv_of_linear_row
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥)
    (hgen : split.unipotentClosure = ⊤) :
    ∃ E : (X ⧸ Q.D) ≃* Sp F,
      split.U.map E.toMonoidHom = unipotent (F := F) ∧
      Q.tits.B.map E.toMonoidHom = Theory.SpecificGroups.SymplecticFour.borel (F := F) ∧
      (((Q.tits.standardParabolic {Q.simple 0}).map E.toMonoidHom = pointParabolic (F := F) ∧
        (Q.tits.standardParabolic {Q.simple 1}).map E.toMonoidHom = planeParabolic (F := F)) ∨
       ((Q.tits.standardParabolic {Q.simple 0}).map E.toMonoidHom = planeParabolic (F := F) ∧
        (Q.tits.standardParabolic {Q.simple 1}).map E.toMonoidHom = pointParabolic (F := F))) := by
  obtain ⟨E⟩ := symplectic_equiv_of_linear_row Q e h split hm μ hq hrow hgen
  obtain ⟨g,E',_,hU⟩ := C2RankThree.exists_unipotent_aligned Q split E
  have hB := C2RankThree.map_borel_of_unipotent Q split E' hU
  exact ⟨E',hU,hB,C2RankThree.map_parabolics_of_borel Q
    (MarkedLocal.parabolic_core_selfCentralizing Q e h) E' hB⟩

include e h in
/-- The full original amalgam comparison, with no remaining geometric premise. -/
theorem comparison_of_linear_row
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥)
    (hgen : split.unipotentClosure = ⊤) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (GreenBook.LieModels.SymplecticFour.amalgam F).reverse) := by
  obtain ⟨E⟩ := symplectic_equiv_of_linear_row Q e h split hm μ hq hrow hgen
  rcases C2RankThree.marked_comparison_of_equiv Q split
    (MarkedLocal.parabolic_core_selfCentralizing Q e h) E with hf | hf
  · exact Or.inl ⟨e.trans hf.some⟩
  · exact Or.inr ⟨e.trans hf.some⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree

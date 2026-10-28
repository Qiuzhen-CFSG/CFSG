module
public import Theory.GroupAction.SymplecticRankThree.Coordinatized
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.LinearGeometry

/-!
# Source C₂ recognition reduced to polar coordinates

The actual local PSL₂ markings and the selected (6A)(a) commutator prove
radical normality, the source kernel bound, and the polarity design on the
same quotient's parabolic cosets. A polar coordinate equivalence then gives
a normal full Sp₄ subgroup by the proved geometric elation argument.
Root-normal-generation identifies it with the whole quotient. The saved
Sylow-normalized comparison retains the full Borel and both endpoint
inclusion squares, in either orientation.

Only the coordinate equivalence and its orthogonality property are new
explicit premises. Their construction from the proved incidence axioms is
still required for the original source theorem. In particular this module
does not assert that source coordinatization has been proved.

Source: Higman (1964), Theorem 2(i), p.154; Fong–Seitz I (6A)(a), pp.36–38;
II (7C), p.193 and (8A), p.197; Aschbacher–Smith F.1.1–12.
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
local notation "a" => C2RankThree.rightCosetPoint Q 1 1
local notation "b" => C2RankThree.neighborPoint Q
local notation "A₀" => MulAction.stabilizer (X ⧸ Q.D) a

local notation "Γ" => MulAction.SwappedOrbital.graph a b (C2RankThree.base_ne_neighbor Q)
  (representative (Q.simple 0) : X ⧸ Q.D)⁻¹
  (C2RankThree.neighbor_swap_base Q) (C2RankThree.neighbor_swap_neighbor Q)

include e h in
/-- Construct the normal symplectic subgroup on the literal source quotient. -/
theorem normal_symplectic_of_polar_coordinates
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥)
    (C : C2RankThree.Points Q 1 ≃ ProjectivePoint F)
    (hC : ∀ x y, Orthogonal (C x) (C y) ↔ y = x ∨ (Γ).Adj x y) :
    ∃ K : Subgroup (X ⧸ Q.D), K.Normal ∧ Nonempty (K ≃* Sp F) := by
  let := marked_coset_faithful Q e h split 1
  obtain ⟨D,hD,hblock,_⟩ := marked_projective_incidence_of_linear_row Q e h split hm μ hq hrow
  have hact : ∀ (g : X ⧸ Q.D) x y, D.incident (g • x) (g • y) ↔ D.incident x y := by
    intro g x y
    rw [hD,hD,MulAction.SwappedOrbital.adj_smul_iff]
    exact or_congr (MulAction.injective g).eq_iff Iff.rfl
  have hfix := C2RankThree.kernelRoot_fixes_of_central Q split hm
    (linear_kernelRoot_central Q split hm μ hq hrow)
  have hk : Nat.card F ≤ Nat.card (fixingSubgroup (X ⧸ Q.D) (D.block a)) := by
    rw [hblock]
    exact C2RankThree.kernel_lower_bound Q split _ (hq 1) hfix
  have hout : ∃ c, ¬ D.incident a c := by
    by_contra! hh
    have he : D.block a = Set.univ := Set.eq_univ_of_forall hh
    have hn := D.block_card a
    change (D.block a).ncard = _ at hn
    rw [he,Set.ncard_univ,C2RankThree.points_card Q split hm (hq 0) (hq 1) 1] at hn
    have hpos : 0 < (Nat.card F)^3 := pow_pos Finite.card_pos _
    omega
  obtain ⟨c,hc⟩ := hout
  exact D.normal_symplectic_of_coordinates C hact (fun x y => (hC x y).trans (hD x y).symm) hc hk

include e h in
/-- Full marked comparison in both orientations after the remaining coordinate construction. -/
theorem comparison_of_polar_coordinates
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥)
    (hgen : split.unipotentClosure = ⊤)
    (C : C2RankThree.Points Q 1 ≃ ProjectivePoint F)
    (hC : ∀ x y, Orthogonal (C x) (C y) ↔ y = x ∨ (Γ).Adj x y) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (GreenBook.LieModels.SymplecticFour.amalgam F).reverse) := by
  obtain ⟨K,hK,⟨model⟩⟩ := normal_symplectic_of_polar_coordinates Q e h split hm μ hq hrow C hC
  let := hK
  exact comparison_of_normal_symplectic Q e h split hm (hq 0) (hq 1) hgen K model

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree

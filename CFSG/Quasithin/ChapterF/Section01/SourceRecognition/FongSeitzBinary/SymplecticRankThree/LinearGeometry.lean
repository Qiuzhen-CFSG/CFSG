module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.LinearNormality
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.SourceGeometry

/-!
# Source C₂ geometry from the actual linear local quotients

The paired local PSL₂ markings identify the literal images of the source
panel actions. Their Sylow orders and the actual simple-root orders prove
the radical normalities of (2B). Thus (3G) and the exact selected (6A)(a)
commutator clause prove the kernel root is central in U and fixes the
closed neighboring orbit. The source coset counts then construct the
polarity design and projective incidence axioms, including q=2.

This removes the radical-normality premise from the original incidence
application. The local markings, common field size and row clause are
earlier producer outputs on this same quotient. For q>2 the subsequent
field coordinatization and symplectic recognition still have to be proved.

Source: Fong–Seitz I (2B), (3G), (6A)(a); II (7C), p.193; Higman (1964), §7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.GroupAction.SymplecticRankThree
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

/-- The exact source row gives centrality of U₂^{s₁} in the same U. -/
theorem linear_kernelRoot_central
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥) :
    split.U ≤ centralizer (C2RankThree.kernelRoot Q split : Set (X ⧸ Q.D)) := by
  let := HexagonStructure.simpleRoot_elementary_of_linear Q split 1 (μ 1)
  exact C2RankThree.kernelRoot_central_of_row Q split hm
    (fun i => C2RankThree.linear_remainder_normalizes Q split i (μ i) (hq i)) hrow

include e h in
/-- All source incidence premises follow from the actual paired local
markings and row clause; radical normality is no longer an assumption. -/
theorem marked_projective_incidence_of_linear_row
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥) :
    ∃ D : PolarityDesign (C2RankThree.Points Q 1) (Nat.card F),
      (∀ x y, D.incident x y ↔ y = x ∨
        (MulAction.SwappedOrbital.graph a b (C2RankThree.base_ne_neighbor Q)
          (representative (Q.simple 0) : X ⧸ Q.D)⁻¹
          (C2RankThree.neighbor_swap_base Q) (C2RankThree.neighbor_swap_neighbor Q)).Adj x y) ∧
      D.block a = insert a (MulAction.orbit A₀ b) ∧
      (∀ x y, x ≠ y → (D.line x y).ncard = Nat.card F+1) ∧
      (∀ x y p, x ≠ y → (D.line x y ∩ D.block p).Nonempty) ∧
      (∀ x y z, x ≠ y → z ∉ D.line x y →
        ∃! p, x ∈ D.block p ∧ y ∈ D.block p ∧ z ∈ D.block p) ∧
      (∀ x y z w, z ≠ w → x ≠ z → y ≠ w →
        (D.line x y ∩ D.line z w).Nonempty → (D.line x z ∩ D.line y w).Nonempty) ∧
      (∃ x y z w, x ≠ y ∧ z ∉ D.line x y ∧
        ¬ ∃ p, x ∈ D.block p ∧ y ∈ D.block p ∧ z ∈ D.block p ∧ w ∈ D.block p) :=
  marked_projective_incidence_of_row Q e h split (by have := Finite.one_lt_card (α := F); omega)
    hm (hq 0) (hq 1)
    (fun i => C2RankThree.linear_remainder_normalizes Q split i (μ i) (hq i)) hrow

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree

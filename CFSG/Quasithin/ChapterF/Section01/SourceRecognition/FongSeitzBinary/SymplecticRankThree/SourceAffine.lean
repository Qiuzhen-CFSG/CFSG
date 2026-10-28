module
public import Theory.GroupAction.SymplecticRankThree.AffineLines
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.LinearGeometry

/-!
# Cartesian charts on the original C₂ parabolic cosets

The original local PSL₂ markings and the selected (6A)(a) commutator clause
construct the polarity design on the same marked quotient. Choose its
closed neighbor block as the plane at infinity. Parallel projection now
constructs a three-axis chart on its complement, with q points on each
axis, the literal parallel-plane fibers, and exhaustive line graphs in the
base plane. A geometric diagonal supplies one common planar scalar alphabet.
No coordinate equivalence, field equations, or recognition
theorem is an input. The construction includes q=2.

These are Cartesian incidence coordinates, not yet projective coordinates
over the source field. Proving field arithmetic and the linear formulas for
the line graphs remains necessary before the nonbinary comparison in
SourceProjective can discharge its coordinate premise. All earlier row and
local-marking producers remain unchanged.

Source: Fong–Seitz I (6A)(a), II (7C), p.193 and (8A), p.197;
Higman (1964), Lemma 10 and Theorem 2(i), pp.153–155.
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
local notation "a₀" => C2RankThree.rightCosetPoint Q 1 1
local notation "b₀" => C2RankThree.neighborPoint Q
local notation "Γ" => MulAction.SwappedOrbital.graph a₀ b₀ (C2RankThree.base_ne_neighbor Q)
  (representative (Q.simple 0) : X ⧸ Q.D)⁻¹
  (C2RankThree.neighbor_swap_base Q) (C2RankThree.neighbor_swap_neighbor Q)

include e h in
/-- The source geometry constructs its Cartesian chart and line graphs;
none of these coordinates are assumed by the original marked input. -/
theorem marked_affine_charts_of_linear_row
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥) :
    ∃ D : PolarityDesign (C2RankThree.Points Q 1) (Nat.card F),
      (∀ x y, D.incident x y ↔ y = x ∨ (Γ).Adj x y) ∧
      ∃ (hl : ∀ x y, x ≠ y → (D.line x y).ncard = Nat.card F+1)
        (f : AffineFrame D),
        f.infinity = a₀ ∧
        ∃ hq' : 2 ≤ Nat.card F,
          (Nat.card (f.AxisI hl hq') = Nat.card F ∧
            Nat.card (f.AxisJ hl hq') = Nat.card F ∧ Nat.card f.Axis = Nat.card F) ∧
          ∃ C : f.Affine ≃ (f.AxisI hl hq' × f.AxisJ hl hq') × f.Axis,
            (∀ (x : f.Affine) (z : f.Axis),
              (x : C2RankThree.Points Q 1) ∈ D.block (f.level hl hq' z.val) ↔
              (C x).2 = z) ∧
            (∀ x y : f.Base hl hq', (x : C2RankThree.Points Q 1) ≠ y →
              (∃ c : f.AxisI hl hq', ∀ z : f.Base hl hq',
                (z : C2RankThree.Points Q 1) ∈ D.line (x : C2RankThree.Points Q 1) y ↔
                  f.first hl hq' z = c) ∨
              (∃ (d : f.Direction hl hq') (hd : (d : C2RankThree.Points Q 1) ≠ f.j)
                (c : f.AxisJ hl hq'), ∀ z : f.Base hl hq',
                (z : C2RankThree.Points Q 1) ∈ D.line (x : C2RankThree.Points Q 1) y ↔
                  f.second hl hq' z = f.graphValue hl hq' d hd c (f.first hl hq' z))) ∧
            (∃ d : f.Direction hl hq', (d : C2RankThree.Points Q 1) ≠ f.i ∧
              (d : C2RankThree.Points Q 1) ≠ f.j ∧
              ∃ E : f.Base hl hq' ≃ f.AxisI hl hq' × f.AxisI hl hq',
                ∀ x : f.Base hl hq', (x : C2RankThree.Points Q 1) ∈ D.line d f.origin ↔
                  (E x).1 = (E x).2) := by
  obtain ⟨D,hD,_,hl,_⟩ := marked_projective_incidence_of_linear_row Q e h split hm μ hq hrow
  have hq' : 2 ≤ Nat.card F := by have := Finite.one_lt_card (α := F); omega
  obtain ⟨f,hf⟩ := D.exists_affineFrame hl hq'
    (C2RankThree.points_card Q split hm (hq 0) (hq 1) 1) a₀
  refine ⟨D,hD,hl,f,hf,hq',f.axes_card hl hq',f.axisCoordinates hl hq',?_,?_,?_⟩
  · exact f.height_fiber hl hq'
  · exact f.line_equations hl hq'
  · obtain ⟨d,hi,hj⟩ := f.exists_diagonal_direction hl hq'
    exact ⟨d,hi,hj,f.scalarCoordinates hl hq' d hi hj,
      f.scalarCoordinates_diagonal hl hq' d hi hj⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree

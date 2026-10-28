module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.SourceField
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Field-linear source geometry in the Chapter12 preparation

Apply the proved scalar-field and planar coordinate construction to the
literal chosen rank-one preparation, its original marked quotient and its
local PSL₂ field. Every actual affine line has its ordinary field equation,
including both the binary and order-four fields. The source F.1.1 hypotheses
are supplied by the existing Chapter12 preparation theorem.

This discharges the planar field-arithmetic part of projective reconstruction.
Full projective coordinates, and therefore the final nonbinary symplectic
comparison, still require the spatial extension. Earlier row and local
marking premises retain their producers; no recognition callback is assumed.

Source: Higman (1964), Lemma 10; Fong–Seitz II (7C), (8A);
Aschbacher–Smith 12.2.2 and F.1.1–12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.SpecificGroups.SymplecticFour
open Theory.GroupAction.SymplecticRankThree
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {F : Type} [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
variable {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P)
local notation "a₀" => C2RankThree.rightCosetPoint Q 1 1
local notation "b₀" => C2RankThree.neighborPoint Q
local notation "Γ" => MulAction.SwappedOrbital.graph a₀ b₀ (C2RankThree.base_ne_neighbor Q)
  (representative (Q.simple 0) : X ⧸ Q.D)⁻¹
  (C2RankThree.neighbor_swap_base Q) (C2RankThree.neighbor_swap_neighbor Q)
include D

/-- Field-linear affine coordinates constructed from the literal Chapter12
preparation and the original selected C₂ row. -/
theorem rankOne_c2_field_plane_of_linear_row
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R)
    (split : SplitData Q.tits)
    (hm : rotationOrder Q = 4)
    (μ : ∀ i, HexagonStructure.localGroup Q split i ≃* PSL(2,F))
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 0 ⊓
          ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1)
        inf_le_left inf_le_right) Q.standardAmalgam) :
    ∃ D : PolarityDesign (C2RankThree.Points Q 1) (Nat.card F),
      (∀ x y, D.incident x y ↔ y = x ∨ (Γ).Adj x y) ∧
      ∃ (hl : ∀ x y, x ≠ y → (D.line x y).ncard = Nat.card F+1)
        (f : AffineFrame D), f.infinity = a₀ ∧
      ∃ (hq' : 2 ≤ Nat.card F) (C : f.Base hl hq' ≃ F × F),
        (∀ a b x : f.Base hl hq',
          (x : C2RankThree.Points Q 1) ∈ SymplecticRankThree.orbitalLine Q a b ↔
            ∃ r : F, C x = C a + r • (C b-C a)) ∧
        (∀ a b : f.Base hl hq', a ≠ b →
          (∃ c : F, ∀ x : f.Base hl hq',
            (x : C2RankThree.Points Q 1) ∈ SymplecticRankThree.orbitalLine Q a b ↔ (C x).1 = c) ∨
          (∃ m c : F, ∀ x : f.Base hl hq',
            (x : C2RankThree.Points Q 1) ∈ SymplecticRankThree.orbitalLine Q a b ↔ (C x).2 = m*(C x).1+c)) := by
  have hf := (D.rankOne_global_local_pair_of_preparation h hmany hn hpsl hH d).1
  exact SymplecticRankThree.marked_field_plane_of_linear_row Q e hf split hm μ hq hrow

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

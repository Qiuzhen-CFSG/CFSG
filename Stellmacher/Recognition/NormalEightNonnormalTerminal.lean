module

public import Stellmacher.Recognition.NormalEightNonnormalSetup
public import Theory.GroupTheory.PGroup.NormalEightFourFusion
public import ABG.ChapterII.Section1.C4SquareWreathedRecognition
public import ABG.ChapterII.Section1.WreathedElementaryRank
public import Theory.SpecificGroups.AffineEight.Basic
public import Theory.SpecificGroups.AffineEight.SimpleSylowExclusion
public import Stellmacher.Recognition.NormalEightTerminalFusionAlternative

/-!+# The fused-four branch at order 32 without a normal elementary eight

Once the three involutions of the normal four fuse in the ambient group,
its centralizer is `C₄ × C₄`. Its index is two, and the Sylow center is
cyclic. The intrinsic extension criterion therefore identifies the Sylow
subgroup as the height-two wreath group, contradicting the supplied
elementary subgroup of order at least eight.

The proofs use only the absence of *normal* elementary eights. The final
assembly helper separates this completed branch from the two ambient
inputs: fusion or the affine-eight alternative, and exclusion of that
alternative as a Sylow subgroup. Neither input is asserted here.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.3–1.4 and §4, printed p.393,
final two paragraphs. `NormalEightNonnormalSetup` supplies the actual
odd-core quotient for the remaining fusion argument.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalTerminal

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- Fusion of the normal four recognizes the wreath group under the
normal-only elementary bound. -/
public theorem isWreathedOfHeight_two_of_fusion
    (S : Sylow 2 G) (hS : Nat.card S = 32)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hfusion : ∀ x y : W, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) :
    ABG.IsWreathedOfHeight S 2 := by
  have hC : IsCyclic (center S) :=
    (S.isPGroup'.to_subgroup (center S)).isCyclic_of_card_omega_one_le_two (by omega)
  have hCi := centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
    S.isPGroup' hZ W hW
  exact ABG.isWreathedOfHeight_two_of_cyclic_center_of_normal_c4_square hS hC
    (centralizer (W : Set S)) (normal_of_index_eq_two hCi)
    (NormalEightFourFusion.centralizer_four_equiv_c4_square S hS hZ hno W hW hfusion)

/-- The elementary subgroup of order at least eight rules out the fused-four branch. -/
public theorem false_of_fusion
    (S : Sylow 2 G) (hS : Nat.card S = 32)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hfusion : ∀ x y : W, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) :
    False := by
  have hbound := ABG.elementary_card_le_four_of_isWreathedOfHeight
    (isWreathedOfHeight_two_of_fusion S hS hZ hno W hW hfusion) A
  omega

/-- Assemble the terminal contradiction from the ambient fusion alternative
and an independently proved affine Sylow exclusion. -/
public theorem false_of_fusion_or_affine
    (S : Sylow 2 G) (hS : Nat.card S = 32)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (haffine : ¬ Nonempty (S ≃* AffineEight.Model))
    (halternative :
      (∀ x y : W, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) ∨
        Nonempty (S ≃* AffineEight.Model)) : False := by
  rcases halternative with hfusion | he
  · exact false_of_fusion S hS A hA hZ hno W hW hfusion
  · exact haffine he

/-- The terminal order-thirty-two branch is impossible in a nonsolvable simple
group. The fusion-or-affine alternative is supplied by the quotient-core
geometry, while the affine alternative is excluded by the intrinsic transfer
argument for `AffineEight.Model`. -/
public theorem false_of_terminal
    [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (hS : Nat.card S = 32)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧
      8 ≤ Nat.card E)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (Stellmacher.Recognition.NormalFourCentralOmegaTwo.fourImage S W).Normal)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16)
    (hindex : (pCore 2 (OmegaQuotient S)).relIndex
      (omegaQuotientSylow S) = 2) : False := by
  have halternative :=
    NormalEightTerminalFusionAlternative.fusion_or_affine hns hN S hS hZ W hW
      hno hunique hnormal hcore hindex
  have haffine : ¬ Nonempty (S ≃* AffineEight.Model) := by
    rintro ⟨e⟩
    exact AffineEight.false_of_simple_sylow hns S e
  apply false_of_fusion_or_affine S hS A hA hZ hno W hW
    haffine
  exact halternative

end Stellmacher.Recognition.NormalEightNonnormalTerminal

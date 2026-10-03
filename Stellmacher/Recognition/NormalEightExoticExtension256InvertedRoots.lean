module

public import Stellmacher.Recognition.NormalEightExoticExtension256ActionSetup
public import Theory.GroupTheory.PGroup.C4SquareSixteenInvertedRoots

/-!
# Inverted order-four elements for the order-256 elementary action

Every element of the elementary sixteen outside the self-centralizing
C₄-square base inverts an element of order four in that base. The conjugation
image has order sixteen; the intrinsic inverted-root theorem applies because
the elementary subgroup centralizes the normal omega four. In particular,
this step needs neither the fixed-point prerequisite nor the ambient fusion
and simplicity assumptions.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.4(c), printed p.386,
applied on p.395.
-/

open Subgroup C4SquareExtension
namespace Stellmacher.Recognition.NormalEightExoticExtension256

/-- Every nontrivial elementary action on the base inverts an element of
order four. The ambient simple-group hypotheses are not needed for this step. -/
public theorem inverted_roots_of_elementary_sixteen
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W D B : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (hW : Nat.card W = 4) (hWB : W ≤ B)
    (hDC : centralizer (D : Set P) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* Model)) (hcard : Nat.card P = 256) :
    ∀ b ∈ B, b ∉ D → ∃ d ∈ D, b * d * b⁻¹ = d⁻¹ ∧ d ^ 2 ≠ 1 := by
  obtain ⟨e⟩ := hmodel
  intro b hb hbD
  apply exists_inverted_root_of_action_card_sixteen hno W D hW hDC hDO e
    (card_conjugation_range D hDC ⟨e⟩ hcard) b
    (elemPow_eq_one_of_isElementaryAbelian b hb) hbD
  intro w hw
  exact B.le_centralizer hb w (hWB hw)

end Stellmacher.Recognition.NormalEightExoticExtension256

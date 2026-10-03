module

public import Theory.GroupTheory.PGroup.C4SquareIndexEight
public import Theory.GroupTheory.PGroup.NormalFourElementaryReplacement

/-!
# Elementary sixteens containing the omega four of a C₄-square

In an order-128 two-group with central omega of order two, an elementary
sixteen can be replaced by one containing the omega four of a normal
C₄-square. Elementary replacement does not decrease its order. The product
with the square lies in the four-centralizer, of order 64, and their
intersection is exactly the four. The product formula bounds the replacement
by sixteen, giving equality.

This discharges the containment premise in the action-image formulas used
for Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), printed p.386.
-/

open Subgroup
namespace C4SquareExtension

/-- An elementary sixteen can be chosen to contain the prescribed omega four. -/
public theorem exists_elementary_sixteen_containing_omega_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcard : Nat.card P = 128)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (W D : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D]
    (hW : Nat.card W = 4)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* Model))
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) :
    ∃ B' : Subgroup P, IsElementaryAbelian 2 B' ∧ Nat.card B' = 16 ∧ W ≤ B' := by
  obtain ⟨B', hBe, hWB, hBB⟩ :=
    hP.exists_elementary_overgroup_normal_four_card_ge W hW B
  let : IsElementaryAbelian 2 B' := hBe
  have hWD : W ≤ D := hO ▸ map_subtype_le _
  have hC : Nat.card (centralizer (W : Set P)) = 64 := by
    have hc := (centralizer (W : Set P)).card_mul_index
    rw [centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
      hP hZ W hW, hcard] at hc
    omega
  have hD : Nat.card D = 16 := by
    obtain ⟨e⟩ := hmodel
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hsup : B' ⊔ D ≤ centralizer (W : Set P) := sup_le
    (B'.le_centralizer.trans (centralizer_le hWB))
    (D.le_centralizer.trans (centralizer_le hWD))
  have hs : Nat.card (B' ⊔ D : Subgroup P) ≤ 64 := hC ▸ card_le_of_le hsup
  have hi := elementary_inf_eq_of_omega_one_eq_four W D B' hO hWB
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes D B'
    (show B' ≤ normalizer (D : Set P) from le_normalizer_of_normal)
  rw [inf_comm D B', sup_comm D B', hi, hD, hW] at hp
  refine ⟨B', hBe, ?_, hWB⟩
  rw [hB] at hBB
  omega

end C4SquareExtension

module

public import Theory.GroupTheory.PGroup.C4SquareSelfCentralizing
public import Theory.GroupTheory.PGroup.NormalFourAbelianBase
public import Theory.GroupTheory.PGroup.RankTwoNormalFour

/-!
# The four-centralizer in a C₄-square extension of order 128

An elementary sixteen containing the omega four of a normal C₄-square
meets that square in precisely the four. Their product therefore has order
64. When the central omega of the whole group has order two, this product
is exactly the index-two centralizer of the normal four.

This is an intrinsic reduction for Janko–Thompson, Math. Z. 113 (1970),
1.4, printed p.386. It does not exclude order 128: the ambient fusion and
normalizer hypotheses are essential to that exclusion.
-/

open Subgroup
namespace C4SquareExtension

/-- The marked C₄-square has index eight in an extension of order 128. -/
public theorem index_eq_eight_of_card_eq_128
    {P : Type*} [Group P] (D : Subgroup P)
    (hmodel : Nonempty (D ≃* Model)) (hcard : Nat.card P = 128) :
    D.index = 8 := by
  obtain ⟨e⟩ := hmodel
  have hD : Nat.card D = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have h := D.card_mul_index
  rw [hD, hcard] at h
  omega

/-- An elementary sixteen and the marked C₄-square generate a group of order 64. -/
public theorem card_sup_eq_sixty_four
    {P : Type*} [Group P] [Finite P]
    (W D B : Subgroup P) [D.Normal] [IsElementaryAbelian 2 B]
    (hW : Nat.card W = 4) (hB : Nat.card B = 16) (hWB : W ≤ B)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* Model)) : Nat.card (B ⊔ D : Subgroup P) = 64 := by
  obtain ⟨e⟩ := hmodel
  have hD : Nat.card D = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hI := elementary_inf_eq_of_omega_one_eq_four W D B hO hWB
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes D B
    (show B ≤ normalizer (D : Set P) from le_normalizer_of_normal)
  rw [inf_comm D B, sup_comm D B, hI, hD, hB, hW] at h
  omega

/-- At order 128 the product is the whole centralizer of the normal four. -/
public theorem centralizer_eq_sup_of_card_eq_128
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (W D B : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (hW : Nat.card W = 4) (hB : Nat.card B = 16) (hWB : W ≤ B)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* Model)) (hcard : Nat.card P = 128) :
    centralizer (W : Set P) = B ⊔ D := by
  have hWD : W ≤ D := hO ▸ map_subtype_le _
  have hBC : B ≤ centralizer (W : Set P) :=
    B.le_centralizer.trans (centralizer_le hWB)
  have hDC : D ≤ centralizer (W : Set P) :=
    D.le_centralizer.trans (centralizer_le hWD)
  have hC := (centralizer (W : Set P)).card_mul_index
  rw [centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
    hP hZ W hW, hcard] at hC
  exact (eq_of_le_of_card_ge (sup_le hBC hDC) (by
    rw [card_sup_eq_sixty_four W D B hW hB hWB hO hmodel]
    omega)).symm

end C4SquareExtension

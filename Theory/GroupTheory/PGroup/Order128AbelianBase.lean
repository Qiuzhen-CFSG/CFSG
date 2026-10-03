module

public import Theory.GroupTheory.PGroup.NormalFourAbelianBase

/-!
# Small normal abelian bases in groups of order 128

A normal elementary four in a finite two-group with no normal elementary
eight extends to a self-centralizing normal abelian rank-two subgroup. If
the group has order 128, a unique central involution and an elementary
sixteen, every such base has index greater than four and order at most
sixteen. Its two cyclic factors therefore have exponents summing to at
most four.

The proof combines normal abelian base existence with the index-four
obstruction and Lagrange's theorem. This is an intrinsic reduction for the
Hall–Janko alternative in Janko–Thompson, Math. Z. 113 (1970), Theorem
1.3(a), printed p.386, citing MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3. It asserts no classification.
-/

open Subgroup

/-- The order-128 hypothesis bounds the actual normal abelian base by sixteen.
The elementary sixteen need not contain the chosen normal four. -/
public theorem IsPGroup.exists_small_normal_abelian_base_of_card_eq_128
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcard : Nat.card P = 128)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) :
    ∃ D : Subgroup P, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
      centralizer (D : Set P) ≤ D ∧
      (omega₁ D (p := 2)).map D.subtype = W ∧ Nat.card D ≤ 16 ∧ 4 < D.index ∧
      ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ n + m ≤ 4 ∧ Nonempty
        (D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m)))) := by
  obtain ⟨D, hWD, hDn, hDa, hDC, hO, n, m, hn, hm, ⟨e⟩⟩ :=
    hP.exists_normal_abelian_base_of_no_normal_eight hno W hW
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  have hi := four_lt_index_of_normal_abelian_of_elementary_sixteen hZ hno B hB D
  have hc := D.card_mul_index
  rw [hcard] at hc
  have hD : Nat.card D = 2 ^ (n + m) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, pow_add]
    simp
  have hsum : n + m ≤ 4 := by
    by_contra! hlarge
    have hp : 32 ≤ Nat.card D := by
      rw [hD]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 5 ≤ n + m)
    nlinarith
  have hsmall : Nat.card D ≤ 16 := by
    rw [hD]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hsum
  exact ⟨D, hWD, hDn, hDa, hDC, hO, hsmall, hi, n, m, hn, hm, hsum, ⟨e⟩⟩


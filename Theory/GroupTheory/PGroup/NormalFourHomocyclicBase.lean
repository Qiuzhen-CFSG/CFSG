module

public import Theory.GroupTheory.PGroup.NormalFourAbelianBase

/-!
# The minimum exponent of a homocyclic abelian base

A self-centralizing subgroup containing an elementary four cannot have order
at most four if an elementary sixteen contains that same four: it would equal
the four, and the sixteen would centralize it. Thus a homocyclic rank-two base
has cyclic factors of order at least four.

This is the elementary lower-exponent step toward Janko–Thompson,
Math. Z. 113 (1970), 1.4, printed p.386, applied on p.395. It does not
establish existence of a homocyclic base or an upper bound on its exponent.
-/

open Subgroup

namespace Subgroup

/-- An elementary sixteen containing the omega four rules out the exponent-two
case of a homocyclic self-centralizing base. -/
public theorem two_le_homocyclic_exponent_of_elementary_sixteen
    {P : Type*} [Group P] [Finite P]
    (W : Subgroup P) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) (hWB : W ≤ B)
    (D : Subgroup P) (hWD : W ≤ D) (hDC : centralizer (D : Set P) ≤ D)
    (n : ℕ) (e : D ≃* (Multiplicative (ZMod (2 ^ n)) ×
      Multiplicative (ZMod (2 ^ n)))) : 2 ≤ n := by
  have hDcard : Nat.card D = 2 ^ n * 2 ^ n := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    simp
  by_contra! hn
  have hDsmall : Nat.card D ≤ 4 := by
    rw [hDcard]
    interval_cases n <;> norm_num
  have hDW : D = W := (eq_of_le_of_card_ge hWD (by omega)).symm
  have hBD : B ≤ D := by
    apply le_trans ?_ hDC
    rw [hDW]
    exact (le_centralizer B).trans (centralizer_le hWB)
  have hh := card_le_of_le hBD
  omega

end Subgroup

/-
Authors: Tianjiao Nie
-/

module

public import FeitThompson.BGsection1.corollary_1_19

open scoped Pointwise

public section

/-
**Kind**: Theorem
**Note**: Theorem 1.20
**Stmt**:
Let $G$ be a finite group with a linear representation on a vector space $V$ over a field $F$.
If the characteristic $F$ is zero or is a prime not dividing $|G|$.
Then $V$ is completely reducible under $G$.
-/

universe u

public theorem theorem_1_20 {G : Type u} [Group G] [Finite G] {F : Type u} [Field F] {V : Type u}
    [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (hchar : ringChar F = 0 ∨ (Nat.Prime (ringChar F) ∧ Nat.Coprime (ringChar F) (Nat.card G))) :
    ρ.IsCompletelyReducible := by
  simpa using
    (Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
      (ρ := ρ) hchar)


end

module

public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Restricting permutation matrices

An injective map intertwining two permutations identifies the smaller
permutation matrix with the corresponding submatrix. Powers and commuting
permutations are transported using Mathlib's row-permutation convention.
These elementary identities support fixed-basis trace comparisons.

Source: the definition of a permutation matrix; the multiplication convention
is `Matrix.permMatrix_mul` in Mathlib.
-/

public section

namespace Matrix
variable {R X Y : Type*}

/-- Restriction along an injective intertwiner preserves permutation matrices. -/
theorem submatrix_permMatrix_of_intertwining [Zero R] [One R]
    [DecidableEq X] [DecidableEq Y]
    (σ : Equiv.Perm X) (τ : Equiv.Perm Y) (e : Y → X)
    (he : Function.Injective e) (h : ∀ y, σ (e y) = e (τ y)) :
    (σ.permMatrix R).submatrix e e = τ.permMatrix R := by
  ext i j
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    h, he.eq_iff]

/-- The row-permutation matrix construction preserves powers. -/
theorem permMatrix_pow [Semiring R] [Fintype X] [DecidableEq X]
    (σ : Equiv.Perm X) (m : ℕ) :
    (σ ^ m).permMatrix R = (σ.permMatrix R) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, permMatrix_mul, ih, ← pow_succ']

/-- Commuting permutations give commuting row-permutation matrices. -/
theorem permMatrix_commute [Semiring R] [Fintype X] [DecidableEq X]
    {σ τ : Equiv.Perm X} (h : Commute σ τ) :
    Commute (σ.permMatrix R) (τ.permMatrix R) := by
  change _ * _ = _ * _
  rw [← permMatrix_mul, ← permMatrix_mul, h.eq]

end Matrix

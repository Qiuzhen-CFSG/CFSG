module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Linarith

/-!
# The tensor-degree induction in G.9.3

For a binary module identified with `I ⊗[F] J`, where the two factors have
the same `F`-dimension `k` and `[F : F₂] = n`, its binary degree is `n*k^2`.
If `n ≤ r` and this degree is at most `2*(2*r+1)`, then the factor degree
is at most `2*(r+1)`. For `k ≥ 2` it is strictly smaller than the original
degree. This supplies the numerical and well-founded parts of the
two-component induction, without assuming a tensor decomposition exists.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
G.9.3, printed p.356. The argument below clears the denominators in the
printed chain of inequalities.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.TensorBounds

open scoped TensorProduct

/-- The factor-degree estimate, with no division and no positivity exceptions. -/
theorem factor_degree_le {n k r : ℕ} (hn : n ≤ r)
    (hd : n * k ^ 2 ≤ 2 * (2 * r + 1)) : n * k ≤ 2 * (r + 1) := by
  by_contra! h
  have hsq : (2 * (r + 1)) ^ 2 < (n * k) ^ 2 := by nlinarith
  have hmul := Nat.mul_le_mul_left n hd
  have hr := Nat.mul_le_mul_right (2 * (2 * r + 1)) hn
  nlinarith

variable {F I J V : Type*} [Field F] [Algebra (ZMod 2) F]
  [AddCommGroup I] [Module F I] [Module (ZMod 2) I] [IsScalarTower (ZMod 2) F I]
  [AddCommGroup J] [Module F J]
  [AddCommGroup V] [Module F V] [Module (ZMod 2) V] [IsScalarTower (ZMod 2) F V]

omit [Module (ZMod 2) I] [IsScalarTower (ZMod 2) F I] in
/-- An actual tensor identification gives the degree used in G.9.3. -/
theorem finrank_eq_square (e : V ≃ₗ[F] I ⊗[F] J)
    (heq : Module.finrank F J = Module.finrank F I) :
    Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) F * Module.finrank F I ^ 2 := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F V, e.finrank_eq,
    Module.finrank_tensorProduct, heq, pow_two]

/-- The small-degree hypothesis descends to a tensor factor. The rank bound
`m ≤ 2*r` and splitting-field bound are genuine inputs still to be constructed
by the group-theoretic part of the two-component proof. -/
theorem factor_small_degree (e : V ≃ₗ[F] I ⊗[F] J)
    (heq : Module.finrank F J = Module.finrank F I)
    {m r : ℕ} (hm : m ≤ 2 * r) (hn : Module.finrank (ZMod 2) F ≤ r)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)) :
    Module.finrank (ZMod 2) I ≤ 2 * (r + 1) := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F I]
  apply factor_degree_le hn
  rw [← finrank_eq_square e heq]
  exact hd.trans (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hm 1))

/-- A nontrivial tensor factor has strictly smaller binary degree, allowing
induction on the degree of the original representation. -/
theorem factor_degree_lt [FiniteDimensional (ZMod 2) F]
    (e : V ≃ₗ[F] I ⊗[F] J)
    (heq : Module.finrank F J = Module.finrank F I)
    (hk : 2 ≤ Module.finrank F I) :
    Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) V := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F I, finrank_eq_square e heq]
  have hn : 0 < Module.finrank (ZMod 2) F := Module.finrank_pos
  have hk' : Module.finrank F I < Module.finrank F I ^ 2 := by nlinarith
  exact Nat.mul_lt_mul_of_pos_left hk' hn

end CFSG.Quasithin.ChapterG.Section09.TensorBounds

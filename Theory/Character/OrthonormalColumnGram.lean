module

public import Theory.Character.ClassFunction

/-!
# Gram matrices of integral columns in an orthonormal family

Expanding both finite sums and using row orthogonality identifies the Hermitian
scalar product of integral linear combinations with the integer column pairing.
This is ordinary finite-dimensional orthonormal expansion.
-/

noncomputable section
open scoped BigOperators

private theorem scalar_sum_left {H I : Type*} [Fintype H] [Fintype I]
    (f : I → ClassFunction H) (g : ClassFunction H) :
    scalarProduct H (∑ i, f i) g = ∑ i, scalarProduct H (f i) g := by
  simp only [scalarProduct, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
private theorem scalar_sum_right {H I : Type*} [Fintype H] [Fintype I]
    (f : ClassFunction H) (g : I → ClassFunction H) :
    scalarProduct H f (∑ i, g i) = ∑ i, scalarProduct H f (g i) := by
  rw [← scalarProduct_conj, scalar_sum_left, star_sum]
  simp only [scalarProduct_conj]

public theorem scalarProduct_integer_columns {H I : Type*} [Fintype H] [Fintype I]
    [DecidableEq I] (f : I → ClassFunction H)
    (hf : ∀ i l, scalarProduct H (f i) (f l) = if i = l then 1 else 0)
    (a b : I → ℤ) :
    scalarProduct H (∑ i, (a i : ℂ) • f i) (∑ i, (b i : ℂ) • f i) =
      (∑ i, a i * b i : ℤ) := by
  rw [scalar_sum_left]
  simp_rw [scalar_sum_right, scalarProduct_smul_left, scalarProduct_smul_right,
    star_intCast, hf]
  simp only [mul_ite, ite_mul, one_mul, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Int.cast_sum, Int.cast_mul]


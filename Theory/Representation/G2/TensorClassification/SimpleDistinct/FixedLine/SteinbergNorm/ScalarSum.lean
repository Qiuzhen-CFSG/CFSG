module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The scalar sum for the G₂ Steinberg norm

The displayed polynomial is a natural-module coefficient times a two-by-two
minor. Over every finite field of characteristic two, the sum of its
`(q - 1)`st powers over the six root parameters is one.

The affine power-sum identity eliminates the last parameter. Translating
`A` by `B * E` then makes the successive sums over `B`, `E`, and `C` affine,
leaving the product of two ordinary power sums. This is a symbolic calculation
uniform in the field size, without enumeration of field elements or tensors.

This supplies the scalar step for the concrete Steinberg norm used in GLS3,
2.8.6–9 and Example 2.8.10(g); the actual tensor coefficient is identified in
`SteinbergNorm.Coefficient`.
-/

@[expose] public section

open scoped BigOperators CharTwo
namespace Atlas.G2.TensorClassification.FixedLine.SteinbergNormCalculation
variable (F : Type*) [Field F] [CharP F 2]

/-- The natural coefficient times the adjacent two-by-two minor. -/
def polynomial (t : Fin 6 → F) : F :=
  (t 0 * t 5 + t 1 * t 3 + t 1 * t 4 * t 5 + t 2 ^ 2) *
    (t 0 ^ 2 + t 0 * t 1 * t 4 + t 0 * t 2 * t 3 + t 1 * t 3 ^ 3 +
      t 2 ^ 3 * t 4 + t 2 ^ 2 * t 3 ^ 2)

variable [Fintype F]

private theorem sum_power : (∑ x : F, x ^ (Fintype.card F - 1)) = 1 := by
  classical
  have hn : Fintype.card F - 1 ≠ 0 := by
    have := Fintype.one_lt_card (α := F)
    omega
  have hp (x : F) : x ^ (Fintype.card F - 1) = if x = 0 then 0 else 1 := by
    by_cases h : x = 0
    · simp [h, hn]
    · simp [h, FiniteField.pow_card_sub_one_eq_one x h]
  have hi (x : F) : (if x = 0 then (0 : F) else 1) = 1 - (if x = 0 then 1 else 0) := by
    split_ifs <;> simp
  simp_rw [hp, hi]
  rw [Finset.sum_sub_distrib]
  simp

private theorem sum_affine (u v : F) :
    (∑ t : F, (u * t + v) ^ (Fintype.card F - 1)) = u ^ (Fintype.card F - 1) := by
  by_cases hu : u = 0
  · have hn : Fintype.card F - 1 ≠ 0 := by
      have := Fintype.one_lt_card (α := F)
      omega
    simp [hu, hn]
  · calc
      _ = ∑ t : F, t ^ (Fintype.card F - 1) :=
        ((Equiv.mulLeft₀ u hu).trans (Equiv.addRight v)).sum_comp _
      _ = 1 := sum_power F
      _ = u ^ (Fintype.card F - 1) := (FiniteField.pow_card_sub_one_eq_one u hu).symm

-- Each identity is uniform in the affine constant, including zero slope.
private theorem sum_affine_mul (z u v : F) :
    (∑ t : F, (z * (u * t + v)) ^ (Fintype.card F - 1)) =
      (z * u) ^ (Fintype.card F - 1) := by
  simp_rw [mul_add, ← mul_assoc]
  exact sum_affine F (z * u) (z * v)

omit [CharP F 2] in
private theorem sum_shift (f : F → F) (a : F) :
    (∑ x : F, f x) = ∑ x : F, f (x + a) := (Equiv.sum_comp (Equiv.addRight a) f).symm

omit [Fintype F] in
private theorem second_shift (x B C D E : F) :
    (x + B * E) ^ 2 + (x + B * E) * B * E + (x + B * E) * C * D +
      B * D ^ 3 + C ^ 3 * E + C ^ 2 * D ^ 2 =
    B * (E * (x + C * D) + D ^ 3) + x ^ 2 + x * C * D + C ^ 3 * E + C ^ 2 * D ^ 2 := by
  ring_nf
  simp

private theorem scalar_sum :
    (∑ A : F, ∑ B : F, ∑ C : F, ∑ D : F, ∑ E : F, ∑ T : F,
      ((A * T + B * D + B * E * T + C ^ 2) * (A ^ 2 + A * B * E + A * C * D + B * D ^ 3 + C ^ 3 * E + C ^ 2 * D ^ 2)) ^
        (Fintype.card F - 1)) = 1 := by
  have ht (A B C D E : F) :
      (∑ T : F,
        ((A * T + B * D + B * E * T + C ^ 2) * (A ^ 2 + A * B * E + A * C * D + B * D ^ 3 + C ^ 3 * E + C ^ 2 * D ^ 2)) ^
          (Fintype.card F - 1)) =
      ((A + B * E) * (A ^ 2 + A * B * E + A * C * D + B * D ^ 3 + C ^ 3 * E + C ^ 2 * D ^ 2)) ^
        (Fintype.card F - 1) := by
    calc
      _ = ∑ T : F,
          (((A + B * E) * (A ^ 2 + A * B * E + A * C * D + B * D ^ 3 + C ^ 3 * E + C ^ 2 * D ^ 2)) * T +
            (B * D + C ^ 2) * (A ^ 2 + A * B * E + A * C * D + B * D ^ 3 + C ^ 3 * E + C ^ 2 * D ^ 2)) ^
              (Fintype.card F - 1) := by
        apply Finset.sum_congr rfl
        intro T _
        congr 1
        ring
      _ = _ := sum_affine F _ _
  simp_rw [ht]
  have ha (B C D E : F) :
      (∑ A : F, ((A + B * E) * (A ^ 2 + A * B * E + A * C * D + B * D ^ 3 + C ^ 3 * E + C ^ 2 * D ^ 2)) ^
        (Fintype.card F - 1)) =
      ∑ x : F, (x * ((E * (x + C * D) + D ^ 3) * B +
        (x ^ 2 + x * C * D + C ^ 3 * E + C ^ 2 * D ^ 2))) ^ (Fintype.card F - 1) := by
    rw [sum_shift F _ (B * E)]
    apply Finset.sum_congr rfl
    intro x _
    rw [second_shift, CharTwo.add_cancel_right]
    congr 2
    ring
  -- Move A inside so its translation may depend on B and E.
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2; ext B
    rw [Finset.sum_comm]
    arg 2; ext C
    rw [Finset.sum_comm]
    arg 2; ext D
    rw [Finset.sum_comm]
  simp_rw [ha]
  -- Move B to the innermost sum, then use the affine identity.
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2; ext C
    rw [Finset.sum_comm]
    arg 2; ext D
    rw [Finset.sum_comm]
    arg 2; ext E
    rw [Finset.sum_comm]
  simp_rw [sum_affine_mul]
  conv_lhs =>
    arg 2; ext C
    arg 2; ext D
    rw [Finset.sum_comm]
  have he (x C D : F) :
      (∑ E : F, (x * (E * (x + C * D) + D ^ 3)) ^ (Fintype.card F - 1)) =
        (x * (x + C * D)) ^ (Fintype.card F - 1) := by
    conv_lhs => simp only [mul_comm (a := _) (b := x + C * D)]
    exact sum_affine_mul F _ _ _
  simp_rw [he]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2; ext D
    rw [Finset.sum_comm]
  have hc (x D : F) :
      (∑ C : F, (x * (x + C * D)) ^ (Fintype.card F - 1)) =
        (x * D) ^ (Fintype.card F - 1) := by
    conv_lhs => simp only [add_comm x, mul_comm (b := D)]
    exact sum_affine_mul F _ _ _
  simp_rw [hc, mul_pow]
  simp_rw [← Finset.sum_mul, sum_power, one_mul]
  exact sum_power F

omit [CharP F 2] in
private theorem sum_fin_cons {n : ℕ} (f : (Fin (n + 1) → F) → F) :
    ∑ t, f t = ∑ a : F, ∑ t : Fin n → F, f (Fin.cons a t) := by
  calc
    _ = ∑ ab : F × (Fin n → F), f (Fin.cons ab.1 ab.2) :=
      Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => F)).symm _ _
        (fun t => congrArg f (Fin.cons_self_tail t).symm)
    _ = _ := Fintype.sum_prod_type _

/-- The six-root polynomial has total power sum one over the entire field. -/
theorem polynomial_sum :
    (∑ t : Fin 6 → F, polynomial F t ^ (Fintype.card F - 1)) = 1 := by
  simp only [polynomial, sum_fin_cons,
    show @Fin.cons 5 (fun _ => F) = Matrix.vecCons from rfl,
    show @Fin.cons 4 (fun _ => F) = Matrix.vecCons from rfl,
    show @Fin.cons 3 (fun _ => F) = Matrix.vecCons from rfl,
    show @Fin.cons 2 (fun _ => F) = Matrix.vecCons from rfl,
    show @Fin.cons 1 (fun _ => F) = Matrix.vecCons from rfl,
    show @Fin.cons 0 (fun _ => F) = Matrix.vecCons from rfl,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fintype.sum_unique]
  exact scalar_sum F

end Atlas.G2.TensorClassification.FixedLine.SteinbergNormCalculation

end

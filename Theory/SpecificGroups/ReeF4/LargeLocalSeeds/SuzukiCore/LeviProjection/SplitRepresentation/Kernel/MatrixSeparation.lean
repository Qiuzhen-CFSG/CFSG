module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection.SplitRepresentation.Kernel.RootAction

/-!
# Separating the split B₂ matrix factors

The positive four-root word has an explicit upper unitriangular matrix, whose
entries recover all four parameters. In a product `U(p) H(a,b) W(k) U(q)`,
every nonidentity Weyl case has a nonzero entry below the diagonal. In the
identity case, the diagonal recovers both torus parameters. Hence a product
equal to one must have trivial torus and Weyl factors.

This is a symbolic calculation at arbitrary field parameters, using units
only for the two torus parameters. Source: the split B₂ Bruhat decomposition
of GLS3 §2.3, used in Aschbacher–Smith F.1.12(I)(5), printed p.263.
-/

set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace ReeF4.LargeLocalSeeds.SuzukiLeviProjection.SplitRepresentation
variable {m : ℕ}
def upperMatrix (p : Fin 4 → CoefficientField m) : Matrix (Fin 4) (Fin 4) (CoefficientField m) :=
  !![1,p 1,p 2,p 3 + p 1*p 2; 0,1,p 0,p 2 + p 0*p 1; 0,0,1,p 1; 0,0,0,1]


theorem upperMatrix_eq_one {p : Fin 4 → CoefficientField m} (h : upperMatrix p = 1) :
    p = fun _ => 0 := by
  have h1 := congrArg (fun A => A 0 1) h
  have h0 := congrArg (fun A => A 1 2) h
  have h2 := congrArg (fun A => A 0 2) h
  have h3 := congrArg (fun A => A 0 3) h
  simp [upperMatrix, Matrix.one_apply] at h0 h1 h2 h3
  ext i
  fin_cases i <;> simp_all

def torusMatrix (a b : (CoefficientField m)ˣ) : Matrix (Fin 4) (Fin 4) (CoefficientField m) :=
  Matrix.diagonal ![b, a * b⁻¹, a⁻¹ * b, b⁻¹]


def representativeMatrix (k : Fin 8) : Matrix (Fin 4) (Fin 4) (CoefficientField m) :=
  ![1, weylMatrix 0, weylMatrix 1, weylMatrix 0 * weylMatrix 1,
    weylMatrix 1 * weylMatrix 0, weylMatrix 0 * weylMatrix 1 * weylMatrix 0,
    weylMatrix 1 * weylMatrix 0 * weylMatrix 1,
    weylMatrix 0 * weylMatrix 1 * weylMatrix 0 * weylMatrix 1] k


theorem normalizer_parameters (p q : Fin 4 → CoefficientField m)
    (a b : (CoefficientField m)ˣ) (k : Fin 8)
    (h : upperMatrix p * (torusMatrix a b * representativeMatrix k) * upperMatrix q = 1) :
    a = 1 ∧ b = 1 ∧ k = 0 := by
  have pivot := congrArg (fun A => A (if k = 1 then 2 else 3)
    ((![0,1,2,2,1,1,0,0] : Fin 8 → Fin 4) k)) h
  fin_cases k
  · have hb := congrArg (fun A => A 0 0) h
    have ha := congrArg (fun A => A 1 1) h
    simp only [upperMatrix, torusMatrix, representativeMatrix, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.diagonal_apply, Matrix.one_apply, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte,
          Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons,
          Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
          zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero] at hb ha
    have hb' : b = 1 := Units.ext hb
    simp only [hb', Units.val_one, inv_one, mul_one] at ha
    exact ⟨Units.ext ha, hb', rfl⟩
  all_goals
    simp only [upperMatrix, torusMatrix, representativeMatrix, weylMatrix,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply, Matrix.one_apply,
      Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte,
          Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons,
          Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
          zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero] at pivot
    simp [a.ne_zero, b.ne_zero] at pivot


end ReeF4.LargeLocalSeeds.SuzukiLeviProjection.SplitRepresentation

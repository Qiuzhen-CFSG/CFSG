module

public import Theory.SpecificGroups.HaradaNorton.MatrixData
public import Mathlib.Algebra.Ring.Commute

/-!
# Algebra behind the HN first-row certificate

The operator `A - I + BABBABBA (B - I)` has zero zeroth row whenever the
specified singleton-row path holds. A right inverse onto the complement of the
zeroth coordinate then annihilates the off-diagonal entries of any commuting
matrix's zeroth row. All matrix algebra is proved with abstract factors before
specialization, to avoid expanding dense word entries during elaboration.
Source of the chosen path: the ATLAS matrices in `../../../MatrixSources.md`.
-/

namespace HaradaNorton.FirstRowCertificate

set_option maxRecDepth 10000

public def word (A B : Matrix133) : Matrix133 :=
  B * (A * (B * (B * (A * (B * (B * A))))))

public def operator (A B : Matrix133) : Matrix133 := A - 1 + word A B * (B - 1)

private theorem single_row_mul (X Y : Matrix133) (i p : Fin 133)
    (h : ∀ k, X i k = if k = p then 1 else 0) (j : Fin 133) :
    (X * Y) i j = Y p j := by simp [Matrix.mul_apply, h]

private theorem row_compose (X Y : Matrix133) (i p q : Fin 133)
    (hX : ∀ k, X i k = if k = p then 1 else 0)
    (hY : ∀ k, Y p k = if k = q then 1 else 0) :
    ∀ j, (X * Y) i j = if j = q then 1 else 0 := by
  intro j
  exact (single_row_mul X Y i p hX j).trans (hY j)

private theorem zero_of_rows (A B W : Matrix133)
    (ha : ∀ k, A 0 k = if k = 0 then 1 else 0)
    (hW : ∀ k, W 0 k = if k = 29 then 1 else 0)
    (hb : ∀ k, B 29 k = if k = 29 then 1 else 0) :
    ∀ j, (A - 1 + W * (B - 1)) 0 j = 0 := by
  intro j
  simp only [Matrix.add_apply, Matrix.sub_apply]
  rw [single_row_mul W (B - 1) 0 29 hW j]
  simp only [Matrix.sub_apply, Matrix.one_apply, ha, hb, eq_comm, sub_self, add_zero]

public theorem operator_zero_row (A B : Matrix133)
    (ha : ∀ k, A 0 k = if k = 0 then 1 else 0)
    (h0 : ∀ k, B 0 k = if k = 1 then 1 else 0)
    (h1 : ∀ k, A 1 k = if k = 2 then 1 else 0)
    (h2 : ∀ k, B 2 k = if k = 4 then 1 else 0)
    (h4 : ∀ k, B 4 k = if k = 7 then 1 else 0)
    (h7 : ∀ k, A 7 k = if k = 10 then 1 else 0)
    (h10 : ∀ k, B 10 k = if k = 15 then 1 else 0)
    (h15 : ∀ k, B 15 k = if k = 21 then 1 else 0)
    (h21 : ∀ k, A 21 k = if k = 29 then 1 else 0)
    (hb : ∀ k, B 29 k = if k = 29 then 1 else 0) :
    ∀ j, operator A B 0 j = 0 := by
  have hW : ∀ j, word A B 0 j = if j = 29 then 1 else 0 := by
    exact (row_compose B (A * (B * (B * (A * (B * (B * A)))))) 0 1 29 h0
      (row_compose A (B * (B * (A * (B * (B * A))))) 1 2 29 h1
      (row_compose B (B * (A * (B * (B * A)))) 2 4 29 h2
      (row_compose B (A * (B * (B * A))) 4 7 29 h4
      (row_compose A (B * (B * A)) 7 10 29 h7
      (row_compose B (B * A) 10 15 29 h10
      (row_compose B A 15 21 29 h15
      h21)))))))
  exact zero_of_rows A B (word A B) ha hW hb

private theorem commute_expression {R : Type*} [Ring R] (A B M : R)
    (ha : Commute M A) (hb : Commute M B) :
    Commute M (A - 1 + (B * (A * (B * (B * (A * (B * (B * A))))))) * (B - 1)) := by
  have hW : Commute M (B * (A * (B * (B * (A * (B * (B * A))))))) :=
    hb.mul_right (ha.mul_right (hb.mul_right (hb.mul_right
      (ha.mul_right (hb.mul_right (hb.mul_right ha))))))
  exact (ha.sub_right (Commute.one_right M)).add_right
    (hW.mul_right (hb.sub_right (Commute.one_right M)))

public theorem commute_operator (A B M : Matrix133) (ha : M * A = A * M)
    (hb : M * B = B * M) : Commute M (operator A B) :=
  commute_expression A B M ha hb

public theorem row_rigidity_of_commute (C D M : Matrix133)
    (hzero : ∀ j, C 0 j = 0)
    (hD : C * D = Matrix.diagonal (fun i : Fin 133 => if i = 0 then 0 else 1))
    (hcomm : M * C = C * M) :
    ∀ j : Fin 133, M 0 j = if j = 0 then M 0 0 else 0 := by
  have hprod (j : Fin 133) : (M * (C * D)) 0 j = 0 := by
    rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc]
    simp only [Matrix.mul_apply, hzero, zero_mul, Finset.sum_const_zero]
  intro j
  by_cases hj : j = 0
  · subst j
    rfl
  · have h := hprod j
    rw [hD, Matrix.mul_diagonal, if_neg hj, mul_one] at h
    simpa only [if_neg hj] using h

public theorem row_rigidity (A B D : Matrix133)
    (hzero : ∀ j, operator A B 0 j = 0)
    (hD : operator A B * D = Matrix.diagonal (fun i : Fin 133 => if i = 0 then 0 else 1))
    (M : Matrix133) (ha : M * A = A * M) (hb : M * B = B * M) :
    ∀ j : Fin 133, M 0 j = if j = 0 then M 0 0 else 0 :=
  row_rigidity_of_commute (operator A B) D M hzero hD (commute_operator A B M ha hb).eq

public theorem operator_mul (A B D : Matrix133) :
    operator A B * D = A * D - D +
      B * (A * (B * (B * (A * (B * (B * (A * (B * D - D)))))))) := by
  simp only [operator, word, add_mul, sub_mul, one_mul, Matrix.mul_assoc]

public theorem inverse_of_products (A B D AD BD X0 X1 X2 X3 X4 X5 X6 X7 X8 P : Matrix133)
    (hAD : A * D = AD) (hBD : B * D = BD) (h0 : BD - D = X0)
    (h1 : A * X0 = X1) (h2 : B * X1 = X2) (h3 : B * X2 = X3)
    (h4 : A * X3 = X4) (h5 : B * X4 = X5) (h6 : B * X5 = X6)
    (h7 : A * X6 = X7) (h8 : B * X7 = X8) (hfinal : AD - D + X8 = P) :
    operator A B * D = P := by
  rw [operator_mul, hAD, hBD, h0, h1, h2, h3, h4, h5, h6, h7, h8, hfinal]

end HaradaNorton.FirstRowCertificate

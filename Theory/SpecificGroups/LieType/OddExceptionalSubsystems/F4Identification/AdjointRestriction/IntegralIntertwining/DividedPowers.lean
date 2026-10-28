module

public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup.IntegralCurves
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Integral divided-power intertwining

An integral intertwiner for first-order operators intertwines their divided
powers: multiply by a factorial and cancel the nonzero integer entrywise.
For two commuting target operators the binomial theorem gives the factorial
of their convolution. Comparing polynomial coefficients then proves the full
product-curve identity, including every degree above the source's cubic bound.
All cancellation takes place over ℤ, before scalar extension.

The concrete consumer is the folded E6--F4 adjoint comparison in the parent
module. The factorial and convolution identities are those of the integral
Geck construction; see GLS3 §§2.2--2.6.
-/

@[expose] public section

open Matrix Polynomial
open RootPairing.SimpleGeckGroup

namespace RootPairing.SimpleGeckGroup.IntegralCubicFamily.Intertwining
variable {m n p κ τ : Type*}

/-- Entrywise polynomial coefficients, retaining the rectangular matrix shape. -/
def coeff (A : Matrix m n (Polynomial ℤ)) (k : ℕ) : Matrix m n ℤ :=
  A.map (fun a => a.coeff k)

/-- Rectangular polynomial matrices are determined by all their coefficients. -/
theorem coeff_ext {A B : Matrix m n (Polynomial ℤ)}
    (h : ∀ k, coeff A k = coeff B k) : A = B := by
  ext x y k
  exact congrFun₂ (h k) x y

/-- The coefficient of a matrix product is the convolution of its coefficients. -/
theorem coeff_mul [Fintype n] (A : Matrix m n (Polynomial ℤ)) (B : Matrix n p (Polynomial ℤ))
    (k : ℕ) : coeff (A * B) k =
      ∑ j ∈ Finset.range (k + 1), coeff A j * coeff B (k - j) := by
  ext x y
  simp only [coeff, Matrix.map_apply, Matrix.mul_apply, Polynomial.finsetSum_coeff,
    Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Matrix.sum_apply]
  exact Finset.sum_comm

/-- A constant right factor may be taken outside coefficient extraction. -/
theorem coeff_mul_const [Fintype n] (A : Matrix m n (Polynomial ℤ)) (B : Matrix n p ℤ)
    (k : ℕ) : coeff (A * B.map (Int.castRingHom (Polynomial ℤ))) k = coeff A k * B := by
  ext x y
  simp [coeff, Matrix.mul_apply]

/-- A constant left factor may be taken outside coefficient extraction. -/
theorem coeff_const_mul [Fintype n] (A : Matrix m n ℤ) (B : Matrix n p (Polynomial ℤ))
    (k : ℕ) : coeff (A.map (Int.castRingHom (Polynomial ℤ)) * B) k = A * coeff B k := by
  ext x y
  simp [coeff, Matrix.mul_apply]

/-- All coefficients of a cubic curve are its integral divided powers. -/
theorem coeff_curve [Fintype n] [DecidableEq n] (D : IntegralCubicFamily κ n) (i : κ)
    (h0 : D.dividedPower i 0 = 1) (k : ℕ) :
    coeff (D.curve i (X : Polynomial ℤ)) k = D.dividedPower i k := by
  rcases k with (_ | _ | _ | _ | k)
  all_goals
    ext x y
    by_cases hxy : x = y <;> simp [hxy, coeff, IntegralCubicFamily.curve, IntegralCubicFamily.coefficient,
      h0, Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
  all_goals rw [D.vanish i (k + 1 + 1 + 1 + 1) (by omega)]; rfl

/-- Rectangular intertwining is preserved by arbitrary powers. -/
theorem pow_intertwines [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix n n ℤ) (B : Matrix m m ℤ) (J : Matrix n m ℤ)
    (h : A * J = J * B) (k : ℕ) : A ^ k * J = J * B ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, h,
      Matrix.mul_assoc]

/-- The commuting binomial expansion equals the factorial times the convolution. -/
theorem factorial_convolution [Fintype n] [DecidableEq n] (D E : ℕ → Matrix n n ℤ)
    (hD : ∀ k, D 1 ^ k = k.factorial • D k)
    (hE : ∀ k, E 1 ^ k = k.factorial • E k)
    (hcomm : Commute (D 1) (E 1)) (k : ℕ) :
    (D 1 + E 1) ^ k = k.factorial •
      ∑ j ∈ Finset.range (k + 1), D j * E (k - j) := by
  rw [hcomm.add_pow, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← nsmul_eq_mul', hD, hE, smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul,
    Nat.choose_mul_factorial_mul_factorial (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)]

/-- First-order intertwining gives every convolution coefficient over ℤ. -/
theorem convolution_intertwines [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (D E : ℕ → Matrix n n ℤ)
    (C : ℕ → Matrix m m ℤ) (J : Matrix n m ℤ)
    (hD : ∀ k, D 1 ^ k = k.factorial • D k)
    (hE : ∀ k, E 1 ^ k = k.factorial • E k)
    (hC : ∀ k, C 1 ^ k = k.factorial • C k)
    (hcomm : Commute (D 1) (E 1))
    (h : (D 1 + E 1) * J = J * C 1) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), D j * E (k - j)) * J = J * C k := by
  have hh := pow_intertwines _ _ J h k
  rw [factorial_convolution D E hD hE hcomm, hC,
    Matrix.smul_mul, Matrix.mul_smul] at hh
  ext x y
  exact nsmul_right_injective (Nat.factorial_ne_zero k) (congrFun₂ hh x y)

/-- Factorial cancellation gives intertwining of each individual divided power. -/
theorem dividedPower_intertwines [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (D : ℕ → Matrix n n ℤ)
    (C : ℕ → Matrix m m ℤ) (J : Matrix n m ℤ)
    (hD : ∀ k, D 1 ^ k = k.factorial • D k)
    (hC : ∀ k, C 1 ^ k = k.factorial • C k)
    (h : D 1 * J = J * C 1) (k : ℕ) : D k * J = J * C k := by
  have hh := pow_intertwines _ _ J h k
  rw [hD, hC, Matrix.smul_mul, Matrix.mul_smul] at hh
  ext x y
  exact nsmul_right_injective (Nat.factorial_ne_zero k) (congrFun₂ hh x y)

/-- An integral first-order identity implies the entire single-curve identity. -/
theorem curve_intertwines [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (D : IntegralCubicFamily κ n) (C : IntegralCubicFamily τ m)
    (i : κ) (j : τ) (J : Matrix n m ℤ)
    (hD : ∀ k, D.dividedPower i 1 ^ k = k.factorial • D.dividedPower i k)
    (hC : ∀ k, C.dividedPower j 1 ^ k = k.factorial • C.dividedPower j k)
    (h : D.dividedPower i 1 * J = J * C.dividedPower j 1) :
    D.curve i (X : Polynomial ℤ) * J.map (Int.castRingHom (Polynomial ℤ)) =
      J.map (Int.castRingHom (Polynomial ℤ)) * C.curve j X := by
  have hD0 : D.dividedPower i 0 = 1 := by simpa using (hD 0).symm
  have hC0 : C.dividedPower j 0 = 1 := by simpa using (hC 0).symm
  apply coeff_ext
  intro k
  rw [coeff_mul_const, coeff_const_mul, coeff_curve D i hD0, coeff_curve C j hC0]
  exact dividedPower_intertwines _ _ J hD hC h k

/-- Two commuting target factors intertwine the source curve in every degree. -/
theorem curve_product_intertwines [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (D : IntegralCubicFamily κ n)
    (C : IntegralCubicFamily τ m) (i j : κ) (a : τ) (J : Matrix n m ℤ)
    (hD : ∀ k, D.dividedPower i 1 ^ k = k.factorial • D.dividedPower i k)
    (hE : ∀ k, D.dividedPower j 1 ^ k = k.factorial • D.dividedPower j k)
    (hC : ∀ k, C.dividedPower a 1 ^ k = k.factorial • C.dividedPower a k)
    (hcomm : Commute (D.dividedPower i 1) (D.dividedPower j 1))
    (h : (D.dividedPower i 1 + D.dividedPower j 1) * J = J * C.dividedPower a 1) :
    (D.curve i (X : Polynomial ℤ) * D.curve j X) * J.map (Int.castRingHom (Polynomial ℤ)) =
      J.map (Int.castRingHom (Polynomial ℤ)) * C.curve a X := by
  have hD0 : D.dividedPower i 0 = 1 := by simpa using (hD 0).symm
  have hE0 : D.dividedPower j 0 = 1 := by simpa using (hE 0).symm
  have hC0 : C.dividedPower a 0 = 1 := by simpa using (hC 0).symm
  apply coeff_ext
  intro k
  rw [coeff_mul_const, coeff_const_mul, coeff_mul, coeff_curve C a hC0]
  simp_rw [coeff_curve D i hD0, coeff_curve D j hE0]
  exact convolution_intertwines _ _ _ J hD hE hC hcomm h k

/-- Degree two of curve commutation recovers commutation of the linear operators. -/
theorem commute_first_of_curves [Fintype n] [DecidableEq n] (D : IntegralCubicFamily κ n) (i j : κ)
    (hD0 : D.dividedPower i 0 = 1) (hE0 : D.dividedPower j 0 = 1)
    (h : Commute (D.curve i (X : Polynomial ℤ)) (D.curve j X)) :
    Commute (D.dividedPower i 1) (D.dividedPower j 1) := by
  have hh := congrArg (fun A => coeff A 2) h.eq
  rw [coeff_mul, coeff_mul] at hh
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    coeff_curve D i hD0, coeff_curve D j hE0] at hh
  norm_num only at hh
  rw [hD0, hE0, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one] at hh
  change _ * _ = _ * _
  have hn : D.dividedPower i 1 * D.dividedPower j 1 +
      (D.dividedPower i 2 + D.dividedPower j 2) =
      D.dividedPower j 1 * D.dividedPower i 1 +
      (D.dividedPower i 2 + D.dividedPower j 2) := by
    convert hh using 1 <;> ac_rfl
  exact add_right_cancel hn

end RootPairing.SimpleGeckGroup.IntegralCubicFamily.Intertwining

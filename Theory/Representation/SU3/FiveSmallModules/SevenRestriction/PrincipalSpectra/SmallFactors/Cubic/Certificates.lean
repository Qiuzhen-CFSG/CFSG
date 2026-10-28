module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors.Cubic.Data
public import Mathlib.Algebra.CharP.Algebra

/-!
# Kernel-checked spectra on the cubic image matrices

Packed products check the exact generator word, its six nonidentity powers,
and invertible changes of basis to the small normal form. Characteristic
polynomials commute with the existing coefficient evaluation, so the result
holds at either nontrivial cubic scalar over every original field.
Source application: Guralnick–Malle, Proposition 4.3, pp.10–11;
Aschbacher–Smith K.2, printed p.453.
-/

public section
namespace Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Cubic
open Degrees.CubicCalculation.ModelFlag Certificate.Packed FactorCoordinates Data

local instance : CharP CoefficientField 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) CoefficientField).injective 2

private theorem word_matrix : matrix 21 W5 = word imageMatrices := by
  have h1 : ∀ i, mul (A 1) (A 0) i = W1 i := by decide +kernel
  have h2 : ∀ i, mul W1 (A 1) i = W2 i := by decide +kernel
  have h3 : ∀ i, mul W2 (A 0) i = W3 i := by decide +kernel
  have h4 : ∀ i, mul W3 (A 0) i = W4 i := by decide +kernel
  have h5 : ∀ i, mul W4 (A 0) i = W5 i := by decide +kernel
  simp only [word, imageMatrices, ← matrix_mul, funext h1, funext h2,
    funext h3, funext h4, funext h5]

private theorem powers_step (k : Fin 6) :
    matrix 21 (powers k.succ) = matrix 21 (powers k.castSucc) * word imageMatrices := by
  have h : ∀ k : Fin 6, ∀ i, mul (powers k.castSucc) W5 i = powers k.succ i :=
    by decide +kernel
  rw [← word_matrix, ← matrix_mul, funext (h k)]

private theorem powers_agreement (k : Fin 7) :
    matrix 21 (powers k) = word imageMatrices ^ k.val := by
  induction k using Fin.induction with
  | zero => exact (matrix_identity 21).trans (pow_zero _).symm
  | succ k ih =>
    simpa only [Fin.val_succ, Fin.val_castSucc, pow_succ] using
      (powers_step k).trans (congrArg (· * word imageMatrices) ih)

private theorem normal_agreement : matrix 21 N = normal CoefficientField := by
  decide +kernel

private theorem intertwining (k : Fin 6) :
    word imageMatrices ^ (k.val + 1) * matrix 21 (basis k) =
      matrix 21 (basis k) * normal CoefficientField := by
  have h : ∀ k : Fin 6, ∀ i,
      mul (powers k.succ) (basis k) i = mul (basis k) N i := by decide +kernel
  have hp : matrix 21 (powers k.succ) = word imageMatrices ^ (k.val + 1) := by
    simpa only [Fin.val_succ] using powers_agreement k.succ
  rw [← normal_agreement, ← hp, ← matrix_mul, ← matrix_mul, funext (h k)]

private theorem inverse_basis (k : Fin 6) :
    matrix 21 (inverseBasis k) * matrix 21 (basis k) = 1 := by
  have h : ∀ k : Fin 6, ∀ i, mul (inverseBasis k) (basis k) i = identity 21 i :=
    by decide +kernel
  rw [← matrix_mul, funext (h k), matrix_identity]

/-- A left inverse and an intertwining identity preserve the polynomial. -/
private theorem charpoly_of_intertwining {F : Type*} [Field F] {n : ℕ}
    (H T B N : Matrix (Fin n) (Fin n) F)
    (hinv : B * T = 1) (hint : H * T = T * N) : H.charpoly = N.charpoly := by
  have hright : T * B = 1 := mul_eq_one_comm.mp hinv
  calc
    H.charpoly = (H * T * B).charpoly := by rw [Matrix.mul_assoc, hright, Matrix.mul_one]
    _ = (T * N * B).charpoly := by rw [hint]
    _ = (B * (T * N)).charpoly := Matrix.charpoly_mul_comm _ _
    _ = N.charpoly := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]

/-- Six finite certificates on the very same image matrices as the literal quotients. -/
theorem coefficient_spectrum (k : ℕ) (hk0 : 0 < k) (hk7 : k < 7) :
    (word imageMatrices ^ k).charpoly = sevenSpectrum CoefficientField 21 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact (charpoly_of_intertwining _ _ _ _ (inverse_basis ⟨j, by omega⟩)
    (intertwining ⟨j, by omega⟩)).trans (normal_spectrum CoefficientField)

/-- Evaluation at the original inverse character scalar preserves the certificate. -/
theorem evaluated_spectrum {K : Type*} [Field K] [CharP K 2]
    (z : K) (hz : z ^ 2 + z + 1 = 0) (k : ℕ) (hk0 : 0 < k) (hk7 : k < 7) :
    ((word imageMatrices ^ k).map (evaluate z hz)).charpoly = sevenSpectrum K 21 := by
  rw [Matrix.charpoly_map, coefficient_spectrum k hk0 hk7]
  simp [sevenSpectrum, sevenPolynomial]

end Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Cubic

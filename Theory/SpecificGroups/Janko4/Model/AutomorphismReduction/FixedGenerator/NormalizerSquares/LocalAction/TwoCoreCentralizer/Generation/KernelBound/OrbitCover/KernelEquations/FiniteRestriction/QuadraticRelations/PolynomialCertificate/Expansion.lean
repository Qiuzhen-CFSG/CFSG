module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Foundation
/-!
# Quadratic coefficients of the restricted matrix equations

A pullback of a fixed form by a linear combination of matrices is quadratic
in the combination coefficients. This module proves its expansion and groups
the ordered products into diagonal terms and unordered pairs. Thus a packed
row can be certified by its constant coefficient and its 7875 upper triangular
coefficients, without quantifying computationally over all coefficient vectors.

The scalar functionals are `upperValue` on the actual restriction matrices.
See `source/README.md` and `../source/README.md` for the coefficient convention
and ATLAS provenance. No numerical coefficient identity is assumed or asserted
without its explicit hypotheses.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate
private theorem sum_upperTriangle {n : ℕ} (f : Fin n → Fin n → ZMod 2) :
    (∑ i, ∑ j, if i ≤ j then f i j + (if i = j then 0 else f j i) else 0) =
      ∑ i, ∑ j, f i j := by
  have h (i j : Fin n) :
      (if i ≤ j then f i j + (if i = j then 0 else f j i) else 0) =
        (if i ≤ j then f i j else 0) + (if i < j then f j i else 0) := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp only [le_of_lt hij, ne_of_lt hij, hij, if_true, if_false]
    · simp
    · simp only [not_le_of_gt hji, not_lt_of_gt hji, if_false, add_zero]
  simp_rw [h, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if i < j then f j i else 0)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i ≤ j
  · simp only [hij, not_lt_of_ge hij, if_true, if_false, add_zero]
  · simp only [hij, lt_of_not_ge hij, if_true, if_false, zero_add]

open GeneratorCertificates
/-- Equality of packed coefficients gives equality for every coefficient vector. -/
theorem eval_of_coefficients (p : ℕ) (c : ZMod 2) (B : Fin 125 → Fin 125 → ZMod 2)
    (hc : bit p 0 = c)
    (hB : ∀ i j, i ≤ j → bit p (slot i j) = B i j + if i = j then 0 else B j i)
    (x : Coefficients) :
    eval p x = c + ∑ i, ∑ j, B i j * (x i * x j) := by
  rw [eval, hc]
  apply congrArg (c + ·)
  calc
    (∑ i, ∑ j, if i ≤ j then bit p (slot i j) * (x i * x j) else 0) =
        ∑ i, ∑ j, if i ≤ j then B i j * (x i * x j) +
          (if i = j then 0 else B j i * (x j * x i)) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i ≤ j
      · rw [if_pos hij, if_pos hij, hB i j hij, add_mul]
        by_cases he : i = j
        · simp only [he, if_true, zero_mul, add_zero]
        · simp only [he, if_false, mul_comm (x j) (x i)]
      · rw [if_neg hij, if_neg hij]
    _ = _ := sum_upperTriangle (fun i j => B i j * (x i * x j))
/-- Upper triangular functionals commute with finite matrix sums. -/
theorem upperValue_sum {α : Type*} (w : ℕ) (s : Finset α) (R : α → RestrictionMatrix) :
    upperValue w (∑ a ∈ s, R a) = ∑ a ∈ s, upperValue w (R a) := by
  let L : RestrictionMatrix →ₗ[ZMod 2] ZMod 2 :=
    { toFun := upperValue w
      map_add' := upperValue_add w
      map_smul' := by intro c R; exact upperValue_smul w c R }
  exact map_sum L R s
/-- Expand pullback in the actual 125 spanning matrices. -/
theorem pullback_coefficientMatrix (x : Coefficients) (R : RestrictionMatrix) :
    (coefficientMatrix x)ᵀ * R * coefficientMatrix x =
      ∑ a : Fin 125, ∑ b : Fin 125,
        (x a * x b) • ((restrictionLinearBasis a)ᵀ * R * restrictionLinearBasis b) := by
  simp only [coefficientMatrix, Matrix.transpose_sum, Matrix.transpose_smul,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm (x b) (x a)]


/-- The ordered bilinear coefficient of an upper triangular pullback test. -/
def pullbackCoefficient (w : ℕ) (R : RestrictionMatrix) (a b : Fin 125) : ZMod 2 :=
  upperValue w ((restrictionLinearBasis a)ᵀ * R * restrictionLinearBasis b)

/-- Scalar expansion of the matrix pullback, before grouping symmetric pairs. -/
theorem upperValue_pullback (w : ℕ) (R : RestrictionMatrix) (x : Coefficients) :
    upperValue w ((coefficientMatrix x)ᵀ * R * coefficientMatrix x) =
      ∑ a, ∑ b, pullbackCoefficient w R a b * (x a * x b) := by
  rw [pullback_coefficientMatrix]
  simp only [upperValue_sum, upperValue_smul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _

/-- A finite coefficient check certifies a packed row against the literal matrix
pullback for all 125-dimensional coefficient vectors. -/
theorem eval_pullback_of_coefficients (p : ℕ) (c : ZMod 2)
    (w : ℕ) (R : RestrictionMatrix) (hc : GeneratorCertificates.bit p 0 = c)
    (hB : ∀ i j, i ≤ j → GeneratorCertificates.bit p (slot i j) =
      pullbackCoefficient w R i j + if i = j then 0 else pullbackCoefficient w R j i)
    (x : Coefficients) :
    eval p x = c + upperValue w ((coefficientMatrix x)ᵀ * R * coefficientMatrix x) := by
  exact (eval_of_coefficients p c (pullbackCoefficient w R) hc hB x).trans
    (congrArg (c + ·) (upperValue_pullback w R x).symm)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate

module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.Construction
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.RoutedCurves
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.DividedPowers

/-!
# Coefficients of positive-simple adjoint equivariance

Write the actual positive curve as `1 + t E + t² B + t³ C`. Applying the
fixed linear adjoint map to one column gives a second cubic expression.
Multiplication has degree at most six. This module writes out its coefficients
and proves that their six matrix identities imply equivariance on that column
for every parameter. It does not assume or assert those root-column identities.

All coefficients use the specialized integral divided powers and the actual
routed coordinate operators from `Construction`. The polynomial formula is
`SimpleGeckGroup.positiveMatrix_formula`, based on Geck's integral construction
in `IntegralGeckConstruction`. F4 has no three-step root strings, so its cubic
divided power vanishes and only degrees one through four need to be checked.
No alternate table of root operators is used.
-/

@[expose] public section

open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup

namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
noncomputable section

/-- The actual integral positive divided power after specialization. -/
def dividedPower (m : ℕ) (i : typeF4RootPairing_base.support) (n : ℕ) :
    Matrix Coordinate Coordinate (CoefficientField m) :=
  (eDividedPower (P := typeF4RootPairing) i n).map (Int.castRingHom (CoefficientField m))

lemma dividedPower_mul (m : ℕ) (i : typeF4RootPairing_base.support) (a b : ℕ) :
    dividedPower m i a * dividedPower m i b =
      (a + b).choose a • dividedPower m i (a + b) := by
  have h := congrArg (fun A : Matrix Coordinate Coordinate ℤ =>
    A.map (Int.castRingHom (CoefficientField m))) (eDividedPower_mul (P := typeF4RootPairing) i a b)
  simpa only [Matrix.map_mul, Matrix.map_smul _ _ (map_nsmul _ _), dividedPower] using h

private lemma cubic_product {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]
    (A U V W E B C : Matrix n n K) (t : K)
    (h1 : U + A * E = E * A)
    (h2 : V + U * E + A * B = B * A)
    (h3 : W + V * E + U * B + A * C = C * A)
    (h4 : W * E + V * B + U * C = 0)
    (h5 : W * B + V * C = 0)
    (h6 : W * C = 0) :
    (A + t • U + t ^ 2 • V + t ^ 3 • W) *
        (1 + t • E + t ^ 2 • B + t ^ 3 • C) =
      (1 + t • E + t ^ 2 • B + t ^ 3 • C) * A := by
  calc
    _ = A + t • (U + A * E) +
        t ^ 2 • (V + U * E + A * B) +
        t ^ 3 • (W + V * E + U * B + A * C) +
        t ^ 4 • (W * E + V * B + U * C) +
        t ^ 5 • (W * B + V * C) + t ^ 6 • (W * C) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        mul_one]
      module
    _ = _ := by
      rw [h1, h2, h3, h4, h5, h6]
      simp only [Matrix.add_mul, Matrix.smul_mul, one_mul, smul_zero, add_zero]

lemma dividedPower_zero (m : ℕ) (i : typeF4RootPairing_base.support) :
    dividedPower m i 0 = 1 := by simp [dividedPower]

lemma dividedPower_eq_zero (m : ℕ) (i : typeF4RootPairing_base.support)
    (n : ℕ) (hn : 4 ≤ n) : dividedPower m i n = 0 := by
  simp [dividedPower, eDividedPower_eq_zero_of_four_le i hn]

/-- The F4 root-length bound kills the cubic divided power already integrally. -/
lemma dividedPower_three_eq_zero (m : ℕ) (i : typeF4RootPairing_base.support) :
    dividedPower m i 3 = 0 := by
  simp [dividedPower, ReeF4.WordRelations.eDividedPower_three]

/-- Apply the fixed adjoint map to a column of a divided power. -/
def columnImage (m : ℕ) (i : typeF4RootPairing_base.support) (n : ℕ) (j : Coordinate) :
    Matrix Coordinate Coordinate (CoefficientField m) :=
  adjointMap m (fun k => dividedPower m i n k j)

lemma columnImage_zero (m : ℕ) (i : typeF4RootPairing_base.support) (j : Coordinate) :
    columnImage m i 0 j = coordinateOperator m j := by
  have h : (fun k => (1 : Matrix Coordinate Coordinate (CoefficientField m)) k j) =
      Pi.single j 1 := by
    classical
    ext k
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [columnImage, dividedPower_zero, h, adjointMap_single]

lemma columnImage_three_eq_zero (m : ℕ) (i : typeF4RootPairing_base.support)
    (j : Coordinate) : columnImage m i 3 j = 0 := by
  rw [columnImage, dividedPower_three_eq_zero]
  exact map_zero _

/-- Coefficients of `D(X(t) e_j) X(t)`, expanded in increasing degree. -/
def curveProductCoefficient (m : ℕ) (i : typeF4RootPairing_base.support)
    (j : Coordinate) : ℕ → Matrix Coordinate Coordinate (CoefficientField m)
  | 0 => coordinateOperator m j
  | 1 => columnImage m i 1 j + coordinateOperator m j * dividedPower m i 1
  | 2 => columnImage m i 2 j + columnImage m i 1 j * dividedPower m i 1 +
      coordinateOperator m j * dividedPower m i 2
  | 3 => columnImage m i 3 j + columnImage m i 2 j * dividedPower m i 1 +
      columnImage m i 1 j * dividedPower m i 2 + coordinateOperator m j * dividedPower m i 3
  | 4 => columnImage m i 3 j * dividedPower m i 1 +
      columnImage m i 2 j * dividedPower m i 2 + columnImage m i 1 j * dividedPower m i 3
  | 5 => columnImage m i 3 j * dividedPower m i 2 + columnImage m i 2 j * dividedPower m i 3
  | 6 => columnImage m i 3 j * dividedPower m i 3
  | _ => 0

/-- Equality of the degree-`d` coefficients in the required adjoint identity. -/
def CoefficientIdentity (m : ℕ) (i : typeF4RootPairing_base.support)
    (j : Coordinate) (d : ℕ) : Prop :=
  curveProductCoefficient m i j d = dividedPower m i d * coordinateOperator m j

lemma adjointMap_positive_column (m : ℕ) (i : typeF4RootPairing_base.support)
    (j : Coordinate) (t : CoefficientField m) :
    adjointMap m (positiveMatrix i t *ᵥ Pi.single j 1) =
      coordinateOperator m j + t • columnImage m i 1 j +
        t ^ 2 • columnImage m i 2 j + t ^ 3 • columnImage m i 3 j := by
  rw [positiveMatrix_formula]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    map_add, map_smul, adjointMap_single]
  simp only [Matrix.mulVec_single_one]
  rfl

/-- The six explicit coefficient identities imply equivariance on a coordinate. -/
lemma basis_of_coefficients (m : ℕ) (i : typeF4RootPairing_base.support)
    (j : Coordinate) (t : CoefficientField m)
    (hc : ∀ d, 1 ≤ d → d ≤ 6 → CoefficientIdentity m i j d) :
    adjointMap m (positiveMatrix i t *ᵥ Pi.single j 1) * positiveMatrix i t =
      positiveMatrix i t * adjointMap m (Pi.single j 1) := by
  have h1 := hc 1 (by omega) (by omega)
  have h2 := hc 2 (by omega) (by omega)
  have h3 := hc 3 (by omega) (by omega)
  have h4 := hc 4 (by omega) (by omega)
  have h5 := hc 5 (by omega) (by omega)
  have h6 := hc 6 (by omega) (by omega)
  have hz4 := dividedPower_eq_zero m i 4 (by omega)
  have hz5 := dividedPower_eq_zero m i 5 (by omega)
  have hz6 := dividedPower_eq_zero m i 6 (by omega)
  simp only [CoefficientIdentity, curveProductCoefficient] at h1 h2 h3
  simp only [CoefficientIdentity, curveProductCoefficient, hz4, zero_mul] at h4
  simp only [CoefficientIdentity, curveProductCoefficient, hz5, zero_mul] at h5
  simp only [CoefficientIdentity, curveProductCoefficient, hz6, zero_mul] at h6
  rw [adjointMap_positive_column, adjointMap_single, positiveMatrix_formula]
  exact cubic_product _ _ _ _ _ _ _ t h1 h2 h3 h4 h5 h6

/-- Degree one is exactly the infinitesimal commutator identity. -/
lemma coefficientIdentity_one_iff (m : ℕ) (i : typeF4RootPairing_base.support)
    (j : Coordinate) :
    CoefficientIdentity m i j 1 ↔
      columnImage m i 1 j = dividedPower m i 1 * coordinateOperator m j -
        coordinateOperator m j * dividedPower m i 1 := by
  change (_ + _ = _) ↔ _ = _ - _
  exact eq_sub_iff_add_eq.symm

/-- With the F4 cubic term zero, four coefficient identities suffice. -/
lemma basis_of_quadratic_coefficients (m : ℕ) (i : typeF4RootPairing_base.support)
    (j : Coordinate) (t : CoefficientField m)
    (hc : ∀ d, 1 ≤ d → d ≤ 4 → CoefficientIdentity m i j d) :
    adjointMap m (positiveMatrix i t *ᵥ Pi.single j 1) * positiveMatrix i t =
      positiveMatrix i t * adjointMap m (Pi.single j 1) := by
  apply basis_of_coefficients m i j t
  intro d hd1 hd6
  by_cases hd4 : d ≤ 4
  · exact hc d hd1 hd4
  · have hz := dividedPower_eq_zero m i d (by omega)
    unfold CoefficientIdentity
    rw [hz, zero_mul]
    interval_cases d <;>
      simp [curveProductCoefficient, columnImage_three_eq_zero, dividedPower_three_eq_zero]

private lemma degree_two_linear (m : ℕ) (i : typeF4RootPairing_base.support)
    (h : ∀ j, CoefficientIdentity m i j 2) (v : Coordinate → CoefficientField m) :
    adjointMap m (dividedPower m i 2 *ᵥ v) +
      adjointMap m (dividedPower m i 1 *ᵥ v) * dividedPower m i 1 +
      adjointMap m v * dividedPower m i 2 =
        dividedPower m i 2 * adjointMap m v := by
  have hv : v = ∑ j, v j • Pi.single j 1 := by
    classical
    ext k
    simp [Pi.single_apply, smul_eq_mul]
  rw [hv]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, map_sum, map_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    ← Finset.sum_add_distrib, ← smul_add]
  apply Finset.sum_congr rfl
  intro j _
  have hj := h j
  unfold CoefficientIdentity curveProductCoefficient at hj
  simpa only [Matrix.mulVec_single_one, adjointMap_single, columnImage,
    Matrix.col_apply'] using
    congrArg (fun A => v j • A) hj

/-- Degree three follows from degree one on this column and degree two on all columns.
The proof applies the latter relation to an image under the first divided power. -/
lemma coefficientIdentity_three_of_one_two (m : ℕ) (i : typeF4RootPairing_base.support)
    (j : Coordinate) (h1 : CoefficientIdentity m i j 1)
    (h2 : ∀ k, CoefficientIdentity m i k 2) : CoefficientIdentity m i j 3 := by
  let E := dividedPower m i 1
  let B := dividedPower m i 2
  let A := coordinateOperator m j
  let U := columnImage m i 1 j
  let V := columnImage m i 2 j
  have hEE : E * E = 0 := by
    have h := dividedPower_mul m i 1 1
    rw [← Nat.cast_smul_eq_nsmul (CoefficientField m)] at h
    change E * E = (2 : CoefficientField m) • B at h
    simpa only [CharTwo.two_eq_zero, zero_smul] using h
  have hBE : B * E = 0 := by
    change dividedPower m i 2 * dividedPower m i 1 = 0
    rw [dividedPower_mul, dividedPower_three_eq_zero, smul_zero]
  have hUB : U * B = B * U := by
    have h := degree_two_linear m i h2 (E *ᵥ Pi.single j 1)
    change adjointMap m (B *ᵥ (E *ᵥ Pi.single j 1)) +
      adjointMap m (E *ᵥ (E *ᵥ Pi.single j 1)) * E +
      adjointMap m (E *ᵥ Pi.single j 1) * B = B * adjointMap m (E *ᵥ Pi.single j 1) at h
    simp only [Matrix.mulVec_mulVec, hEE, hBE, Matrix.zero_mulVec, map_zero,
      Matrix.zero_mul, zero_add] at h
    simpa only [Matrix.mulVec_single_one, U, columnImage, E, Matrix.col_apply'] using h
  have h2j := h2 j
  change V + U * E + A * B = B * A at h2j
  change U + A * E = E * A at h1
  have hVE : V * E = B * A * E := by
    have h := congrArg (fun Z => Z * E) h2j
    simpa only [Matrix.add_mul, mul_assoc, hEE, hBE, Matrix.mul_zero, add_zero] using h
  have hBU : B * U + B * A * E = 0 := by
    have h := congrArg (fun Z => B * Z) h1
    simpa only [Matrix.mul_add, ← mul_assoc, hBE, Matrix.zero_mul] using h
  simp only [CoefficientIdentity, curveProductCoefficient, columnImage_three_eq_zero,
    dividedPower_three_eq_zero, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
  change V * E + U * B = 0
  rw [hVE, hUB, add_comm]
  exact hBU


end
end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple

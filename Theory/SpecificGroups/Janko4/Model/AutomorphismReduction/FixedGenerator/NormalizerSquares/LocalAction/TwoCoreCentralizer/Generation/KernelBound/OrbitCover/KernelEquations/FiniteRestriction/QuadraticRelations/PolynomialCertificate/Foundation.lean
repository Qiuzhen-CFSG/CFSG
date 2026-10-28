module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.RestrictionData
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.Packed
/-!
# Evaluation interfaces for the finite restriction certificate

Write a restriction matrix as a linear combination of its 125 published
spanning matrices. Packed natural numbers encode quadratic polynomials over
GF(2): bit zero is the constant coefficient, followed by the pairs `i ≤ j`
in lexicographic order. Diagonal monomials evaluate as `x i * x i`; the
Boolean identity is proved separately, so substitution must account for it.

Upper triangular matrix tests are linear functionals on the actual restricted
forms. A test annihilating their 1221 generators annihilates the entire span.
Pairing preservation and exterior membership therefore give zero evaluations
of these matrix tests. Connecting the numerical polynomial rows to the tests,
and certifying the subsequent elimination, are separate obligations.

Source and ATLAS matrix conventions: `../source/README.md` and
`OrbitCover/Coordinates.lean`. The coefficient ordering is the retained
`orthogonal.py` calculation, documented in `source/README.md` below this module.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate
open GeneratorCertificates
/-- Coefficients in the displayed 125-element spanning family. -/
abbrev Coefficients := Fin 125 → ZMod 2
/-- Synthesize a restriction matrix; independence of the generators is unnecessary. -/
def coefficientMatrix (x : Coefficients) : RestrictionMatrix :=
  ∑ a, x a • restrictionLinearBasis a
theorem exists_coefficients_of_mem {S : RestrictionMatrix} (h : S ∈ restrictionLinearSpace) :
    ∃ x : Coefficients, coefficientMatrix x = S := by
  exact (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp h
theorem coordinates_coefficientMatrix (x : Coefficients) (i : Fin 22) :
    coordinates (restrictionImage (coefficientMatrix x)) i =
      ∑ a, x a * coordinates (restrictionImage (restrictionLinearBasis a)) i := by
  simp only [coefficientMatrix, restrictionImage, coordinates, Matrix.sum_mulVec,
    Matrix.mulVec_sum, dotProduct_sum, Matrix.smul_mulVec, Matrix.mulVec_smul,
    dotProduct_smul, smul_eq_mul]

/-- Saved-table bit position of `x i * x j`, used only when `i ≤ j`. -/
def slot (i j : Fin 125) : ℕ :=
  1 + i.val * 125 - i.val * (i.val - 1) / 2 + (j.val - i.val)
/-- Evaluate the constant and upper triangular quadratic coefficients. -/
def eval (p : ℕ) (x : Coefficients) : ZMod 2 :=
  bit p 0 + ∑ i : Fin 125, ∑ j : Fin 125,
    if i ≤ j then bit p (slot i j) * (x i * x j) else 0
theorem eval_zero (x : Coefficients) : eval 0 x = 0 := by simp [eval, bit]
theorem eval_xor (p q : ℕ) (x : Coefficients) :
    eval (p ^^^ q) x = eval p x + eval q x := by
  unfold eval
  simp_rw [bit_xor]
  have h (i j : Fin 125) :
      (if i ≤ j then (bit p (slot i j) + bit q (slot i j)) * (x i * x j) else 0) =
        (if i ≤ j then bit p (slot i j) * (x i * x j) else 0) +
        (if i ≤ j then bit q (slot i j) * (x i * x j) else 0) := by
    by_cases hij : i ≤ j
    · simp only [hij, if_true, add_mul]
    · simp only [hij, if_false, add_zero]
  have hs : (∑ i : Fin 125, ∑ j : Fin 125,
      if i ≤ j then (bit p (slot i j) + bit q (slot i j)) * (x i * x j) else 0) =
      (∑ i : Fin 125, ∑ j : Fin 125,
        if i ≤ j then bit p (slot i j) * (x i * x j) else 0) +
      (∑ i : Fin 125, ∑ j : Fin 125,
        if i ≤ j then bit q (slot i j) * (x i * x j) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact h i j
  rw [hs]
  exact add_add_add_comm _ _ _ _
theorem square_eq_self (x : ZMod 2) : x*x = x := by
  have h : ∀ a : ZMod 2, a*a = a := by decide
  exact h x

theorem eval_xorList (ps : List ℕ) (x : Coefficients) :
    eval (xorList ps) x = (ps.map (fun p => eval p x)).sum := by
  induction ps with
  | nil => simp [xorList, eval_zero]
  | cons p ps ih => simp only [xorList, eval_xor, ih, List.map_cons, List.sum_cons]

/-- Zero-based upper triangular entry position, used only for `i < j`. -/
def upperSlot (i j : Fin 50) : ℕ :=
  i.val * 50 - i.val * (i.val + 1) / 2 + (j.val - i.val - 1)
/-- A linear functional on 50 by 50 matrices, in upper triangular entry order. -/
def upperValue (w : ℕ) (R : RestrictionMatrix) : ZMod 2 :=
  ∑ i : Fin 50, ∑ j : Fin 50,
    (if i < j then bit w (upperSlot i j) else 0) * R i j
theorem upperValue_add (w : ℕ) (R T : RestrictionMatrix) :
    upperValue w (R + T) = upperValue w R + upperValue w T := by
  simp only [upperValue, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
theorem upperValue_smul (w : ℕ) (c : ZMod 2) (R : RestrictionMatrix) :
    upperValue w (c • R) = c * upperValue w R := by
  simp only [upperValue, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_left_comm _ _ _
theorem upperValue_zero (w : ℕ) : upperValue w 0 = 0 := by simp [upperValue]

/-- A Gaussian combination certificate transports vanishing evaluations. -/
theorem eval_zero_of_xor {n : ℕ} (rows : Vector ℕ n) (indices : List (Fin n))
    (target : ℕ) (hcert : xorList (indices.map rows.get) = target)
    (x : Coefficients) (hrows : ∀ i, eval (rows.get i) x = 0) :
    eval target x = 0 := by
  rw [← hcert, eval_xorList, List.map_map]
  have h : (indices.map (fun i => eval (rows.get i) x)).sum = 0 := by
    clear hcert
    induction indices with
    | nil => rfl
    | cons i is ih => rw [List.map_cons, List.sum_cons, hrows i, ih, zero_add]
  exact h

/-- It suffices to check a functional on the original 1221 exterior generators. -/
theorem upperValue_zero_of_mem (w : ℕ)
    (hw : ∀ a : Fin 1221, upperValue w (restrictionForm (exteriorBasisForm a)) = 0)
    {R : RestrictionMatrix} (hR : R ∈ restrictionExteriorSpace) :
    upperValue w R = 0 := by
  induction hR using Submodule.span_induction with
  | mem R hR =>
    obtain ⟨a, rfl⟩ := hR
    exact hw a
  | zero => exact upperValue_zero w
  | add R T _ _ hR hT => rw [upperValue_add, hR, hT, add_zero]
  | smul c R _ hR => rw [upperValue_smul, hR, mul_zero]

/-- Block zero is the pairing; blocks one through nine are the actual test forms. -/
def testForm (b : Fin 10) : RestrictionMatrix :=
  if h : b.val = 0 then restrictionPairing
  else restrictionTestForm ⟨b.val - 1, by omega⟩

/-- A scalar equation from pairing preservation or exterior membership. -/
def constraintValue (test : Fin 10 × ℕ) (S : RestrictionMatrix) : ZMod 2 :=
  upperValue test.2 (Sᵀ * testForm test.1 * S) +
    if test.1.val = 0 then upperValue test.2 restrictionPairing else 0

/-- Soundness of an annihilating upper triangular test. This does not assert
that any numerical table is such a test. -/
theorem constraintValue_zero (test : Fin 10 × ℕ) (S : RestrictionMatrix)
    (hpair : Sᵀ * restrictionPairing * S = restrictionPairing)
    (hext : ∀ i : Fin 9, Sᵀ * restrictionTestForm i * S ∈ restrictionExteriorSpace)
    (htest : test.1.val ≠ 0 → ∀ a : Fin 1221,
      upperValue test.2 (restrictionForm (exteriorBasisForm a)) = 0) :
    constraintValue test S = 0 := by
  by_cases hb : test.1.val = 0
  · simp only [constraintValue, testForm, hb, ↓reduceDIte, ↓reduceIte, hpair]
    have h : ∀ z : ZMod 2, z + z = 0 := by decide
    exact h _
  · simp only [constraintValue, testForm, hb, ↓reduceDIte, ↓reduceIte, add_zero]
    exact upperValue_zero_of_mem _ (htest hb) (hext _)

/-- The numerical target uses the product with the zeroth coordinate.
Normalization is therefore required to recover the stated chart equation. -/
theorem quadratic_eq_of_normalized_target (v : NaturalModule) (i : Fin 9)
    (hnorm : coordinates v 0 = 1)
    (htarget : coordinates v 0 * coordinates v (quadraticIndex i) +
      quadraticCoordinate i (freeCoordinates v) = 0) :
    coordinates v (quadraticIndex i) = quadraticCoordinate i (freeCoordinates v) := by
  rw [hnorm, one_mul] at htarget
  have h : ∀ z : ZMod 2, z + z = 0 := by decide
  exact add_right_cancel (htarget.trans (h _).symm)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate

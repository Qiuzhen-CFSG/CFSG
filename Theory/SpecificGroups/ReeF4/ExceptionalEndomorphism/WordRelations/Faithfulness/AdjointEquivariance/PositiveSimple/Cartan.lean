module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.Coefficients
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Relations

/-!
# Positive-simple equivariance on Cartan coordinates

The integral Cartan commutator acts on the n-th positive divided power with
weight n times the Cartan integer. Cancel factorials over the integers before
specializing to characteristic two. These weights and divided-power products
prove the positive-curve identity on every Cartan basis vector.

The source is the simple sl₂ relations in Geck’s construction, implemented in
`GeckConstruction.Relations` and `IntegralGeckConstruction`.
-/

@[expose] public section

open scoped Matrix CharTwo
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup

namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
noncomputable section

private def integralCartan (j : typeF4RootPairing_base.support) : Matrix Coordinate Coordinate ℤ :=
  eMatrix (P := typeF4RootPairing) j * fMatrix j - fMatrix j * eMatrix j

private lemma integralCartan_e (i j : typeF4RootPairing_base.support) :
    integralCartan j * eMatrix (P := typeF4RootPairing) i -
      eMatrix i * integralCartan j =
      typeF4RootPairing_base.cartanMatrix i j • eMatrix i := by
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ ℝ)
  dsimp only
  simp only [integralCartan, Matrix.map_sub _ (map_sub _), Matrix.map_mul,
    Matrix.map_smul _ _ (map_zsmul _ _), map_eMatrix, map_fMatrix]
  have h := RootPairing.GeckConstruction.lie_h_e (P := typeF4RootPairing) i j
  rw [← RootPairing.GeckConstruction.lie_e_f_same j] at h
  exact h

private lemma commutator_pow {A : Type*} [Ring A] (H E : A) (a : ℤ)
    (h : H * E - E * H = a • E) (n : ℕ) :
    H * E ^ n - E ^ n * H = ((n : ℤ) * a) • E ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      H * E ^ (n + 1) - E ^ (n + 1) * H =
          (H * E ^ n - E ^ n * H) * E + E ^ n * (H * E - E * H) := by
        rw [pow_succ]
        noncomm_ring
      _ = (((n : ℤ) + 1) * a) • E ^ (n + 1) := by
        rw [ih, h, smul_mul_assoc, mul_smul_comm, ← add_zsmul, ← pow_succ]
        congr 1
        ring
      _ = _ := by simp

private lemma integralCartan_dividedPower (i j : typeF4RootPairing_base.support) (n : ℕ) :
    integralCartan j * eDividedPower (P := typeF4RootPairing) i n -
      eDividedPower i n * integralCartan j =
      ((n : ℤ) * typeF4RootPairing_base.cartanMatrix i j) • eDividedPower i n := by
  have h := commutator_pow (integralCartan j) (eMatrix (P := typeF4RootPairing) i)
    (typeF4RootPairing_base.cartanMatrix i j) (integralCartan_e i j) n
  rw [eMatrix_pow_eq_factorial_smul] at h
  simp only [← Nat.cast_smul_eq_nsmul ℤ, Matrix.mul_smul, Matrix.smul_mul] at h
  ext x y
  have hxy := congrFun (congrFun h x) y
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hxy
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have hn : (n.factorial : ℤ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  apply (mul_left_cancel₀ hn)
  linear_combination hxy

private lemma map_integralCartan (m : ℕ) (j : typeF4RootPairing_base.support) :
    (integralCartan j).map (Int.castRingHom (CoefficientField m)) =
      coordinateOperator m (Sum.inl j) := by
  simp only [integralCartan, coordinateOperator, Matrix.map_sub _ (map_sub _), Matrix.map_mul]

private lemma cartan_dividedPower (m : ℕ) (i j : typeF4RootPairing_base.support) (n : ℕ) :
    coordinateOperator m (Sum.inl j) * dividedPower m i n -
      dividedPower m i n * coordinateOperator m (Sum.inl j) =
      ((n : ℤ) * typeF4RootPairing_base.cartanMatrix i j) • dividedPower m i n := by
  have h := congrArg (fun A : Matrix Coordinate Coordinate ℤ =>
    A.map (Int.castRingHom (CoefficientField m))) (integralCartan_dividedPower i j n)
  simpa only [Matrix.map_sub _ (map_sub _), Matrix.map_mul,
    Matrix.map_smul _ _ (map_zsmul _ _), map_integralCartan, dividedPower] using h

private lemma cast_abs (m : ℕ) (a : ℤ) : ((|a| : ℤ) : CoefficientField m) = (a : CoefficientField m) := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, Int.cast_neg, CharTwo.neg_eq]

private lemma positiveMatrix_cartan (m : ℕ) (i j : typeF4RootPairing_base.support)
    (t : CoefficientField m) :
    (coordinateOperator m (Sum.inl j) +
        (t * (|typeF4RootPairing_base.cartanMatrix i j| : ℤ)) • dividedPower m i 1) *
        positiveMatrix i t = positiveMatrix i t * coordinateOperator m (Sum.inl j) := by
  let H := coordinateOperator m (Sum.inl j)
  let E := dividedPower m i 1
  let B := dividedPower m i 2
  let C := dividedPower m i 3
  let a : CoefficientField m := typeF4RootPairing_base.cartanMatrix i j
  have htwo : (2 : CoefficientField m) = 0 := CharTwo.two_eq_zero
  have hthree : (3 : CoefficientField m) = 1 := by
    simpa only [Nat.reduceMod, Nat.cast_one, Nat.cast_ofNat] using
      (CharTwo.natCast_eq_mod (R := CoefficientField m) 3)
  have hfour : (4 : CoefficientField m) = 0 := by
    simpa only [Nat.reduceMod, Nat.cast_zero, Nat.cast_ofNat] using
      (CharTwo.natCast_eq_mod (R := CoefficientField m) 4)
  have h1 : H * E = E * H + a • E := by
    have h := cartan_dividedPower m i j 1
    simpa only [Nat.cast_one, one_mul, ← Int.cast_smul_eq_zsmul (CoefficientField m), add_comm] using
      (sub_eq_iff_eq_add.mp h)
  have h2 : H * B = B * H := by
    have h := cartan_dividedPower m i j 2
    rw [← Int.cast_smul_eq_zsmul (CoefficientField m)] at h
    simp only [Int.cast_mul] at h
    change H * B - B * H = ((2 : CoefficientField m) * a) • B at h
    rw [htwo, zero_mul, zero_smul] at h
    exact sub_eq_zero.mp h
  have h3 : H * C = C * H + a • C := by
    have h := cartan_dividedPower m i j 3
    rw [← Int.cast_smul_eq_zsmul (CoefficientField m)] at h
    simp only [Int.cast_mul] at h
    change H * C - C * H = ((3 : CoefficientField m) * a) • C at h
    rw [hthree, one_mul] at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have hEE : E * E = 0 := by
    have h := dividedPower_mul m i 1 1
    rw [← Nat.cast_smul_eq_nsmul (CoefficientField m)] at h
    change E * E = (2 : CoefficientField m) • B at h
    simpa only [htwo, zero_smul] using h
  have hEB : E * B = C := by
    have h := dividedPower_mul m i 1 2
    rw [← Nat.cast_smul_eq_nsmul (CoefficientField m)] at h
    change E * B = (3 : CoefficientField m) • C at h
    simpa only [hthree, one_smul] using h
  have hEC : E * C = 0 := by
    have h := dividedPower_mul m i 1 3
    rw [← Nat.cast_smul_eq_nsmul (CoefficientField m)] at h
    change E * C = (4 : CoefficientField m) • dividedPower m i 4 at h
    simpa only [hfour, zero_smul] using h
  rw [positiveMatrix_formula, cast_abs]
  change (H + (t * a) • E) * (1 + t • E + t ^ 2 • B + t ^ 3 • C) =
    (1 + t • E + t ^ 2 • B + t ^ 3 • C) * H
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_one, one_mul, hEE, hEB, hEC, smul_zero, add_zero, h1, h2, h3]
  match_scalars <;> ring_nf <;> simp only [htwo, mul_zero]

lemma coordinateOperator_simple (m : ℕ) (i : typeF4RootPairing_base.support) :
    coordinateOperator m (Sum.inr i) = dividedPower m i 1 := by
  change (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) i).map _ = _
  rw [rootOperator_simple]
  rfl

private lemma cast_mulVec (m : ℕ) (A : Matrix Coordinate Coordinate ℤ) (v : Coordinate → ℤ) :
    (Int.castRingHom (CoefficientField m)) ∘ (A *ᵥ v) =
      A.map (Int.castRingHom (CoefficientField m)) *ᵥ
        ((Int.castRingHom (CoefficientField m)) ∘ v) := by
  ext i
  exact (Int.castRingHom (CoefficientField m)).map_mulVec A v i

private lemma cast_single (m : ℕ) (j : Coordinate) :
    (Int.castRingHom (CoefficientField m)) ∘ Pi.single j (1 : ℤ) = Pi.single j 1 := by
  classical
  ext i
  simp [Pi.single_apply]

private lemma dividedPower_mulVec_cartan_one (m : ℕ) (i j : typeF4RootPairing_base.support) :
    dividedPower m i 1 *ᵥ Pi.single (Sum.inl j) 1 =
      (|typeF4RootPairing_base.cartanMatrix i j| : ℤ) • Pi.single (Sum.inr (i : typeF4Roots) : Coordinate) (1 : CoefficientField m) := by
  have h := congrArg (fun v : Coordinate → ℤ =>
    (Int.castRingHom (CoefficientField m)) ∘ v) (eMatrix_mulVec_u (P := typeF4RootPairing) i j)
  have cast_smul (z : ℤ) (v : Coordinate → ℤ) :
      (Int.castRingHom (CoefficientField m)) ∘ (z • v) =
        z • ((Int.castRingHom (CoefficientField m)) ∘ v) := by ext k; simp
  rw [cast_mulVec, cast_smul] at h
  rw [u, v, cast_single, cast_single] at h
  exact h

private lemma dividedPower_mulVec_cartan_high (m : ℕ) (i j : typeF4RootPairing_base.support) (n : ℕ) :
    dividedPower m i (n + 2) *ᵥ Pi.single (Sum.inl j) 1 = 0 := by
  have h := congrArg (fun v : Coordinate → ℤ =>
    (Int.castRingHom (CoefficientField m)) ∘ v)
    (eDividedPower_add_two_mulVec_u (P := typeF4RootPairing) i j n)
  rw [cast_mulVec] at h
  rw [u, cast_single] at h
  ext x
  have hx := congrFun h x
  simpa only [dividedPower, Function.comp_apply, Pi.zero_apply, map_zero] using hx

private lemma positiveMatrix_mulVec_cartan (m : ℕ) (i j : typeF4RootPairing_base.support)
    (t : CoefficientField m) :
    positiveMatrix i t *ᵥ Pi.single (Sum.inl j) 1 =
      Pi.single (Sum.inl j : Coordinate) (1 : CoefficientField m) +
        (t * (|typeF4RootPairing_base.cartanMatrix i j| : ℤ)) • Pi.single (Sum.inr (i : typeF4Roots) : Coordinate) (1 : CoefficientField m) := by
  rw [positiveMatrix_formula]
  change (1 + t • dividedPower m i 1 + t ^ 2 • dividedPower m i (0 + 2) +
    t ^ 3 • dividedPower m i (1 + 2)) *ᵥ _ = _
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dividedPower_mulVec_cartan_one, dividedPower_mulVec_cartan_high, smul_zero, add_zero,
    ← Int.cast_smul_eq_zsmul (CoefficientField m), smul_smul]

lemma positive_cartan_basis (m : ℕ) (i j : typeF4RootPairing_base.support)
    (t : CoefficientField m) :
    adjointMap m (positiveMatrix i t *ᵥ Pi.single (Sum.inl j) 1) * positiveMatrix i t =
      positiveMatrix i t * adjointMap m (Pi.single (Sum.inl j) 1) := by
  rw [positiveMatrix_mulVec_cartan, map_add, map_smul, adjointMap_single,
    adjointMap_single, coordinateOperator_simple]
  exact positiveMatrix_cartan m i j t

/-- Each of the four Cartan coefficients is already determined by the simple weights. -/
lemma coefficientIdentity_cartan (m : ℕ) (i j : typeF4RootPairing_base.support)
    (d : ℕ) (hd1 : 1 ≤ d) (hd4 : d ≤ 4) :
    CoefficientIdentity m i (Sum.inl j) d := by
  let a : CoefficientField m := typeF4RootPairing_base.cartanMatrix i j
  have hu : columnImage m i 1 (Sum.inl j) = a • dividedPower m i 1 := by
    change adjointMap m ((dividedPower m i 1).col (Sum.inl j)) = _
    rw [← Matrix.mulVec_single_one, dividedPower_mulVec_cartan_one,
      ← Int.cast_smul_eq_zsmul (CoefficientField m), map_smul, adjointMap_single,
      coordinateOperator_simple, cast_abs]
  have hv : columnImage m i 2 (Sum.inl j) = 0 := by
    change adjointMap m ((dividedPower m i 2).col (Sum.inl j)) = _
    rw [← Matrix.mulVec_single_one]
    have h := dividedPower_mulVec_cartan_high m i j 0
    rw [h, map_zero]
  have h1 := cartan_dividedPower m i j 1
  rw [← Int.cast_smul_eq_zsmul (CoefficientField m)] at h1
  have h2 := cartan_dividedPower m i j 2
  rw [← Int.cast_smul_eq_zsmul (CoefficientField m)] at h2
  have hEE : dividedPower m i 1 * dividedPower m i 1 = 0 := by
    have h := dividedPower_mul m i 1 1
    rw [← Nat.cast_smul_eq_nsmul (CoefficientField m)] at h
    change _ = (2 : CoefficientField m) • dividedPower m i 2 at h
    simpa only [CharTwo.two_eq_zero, zero_smul] using h
  have hEB : dividedPower m i 1 * dividedPower m i 2 = 0 := by
    rw [dividedPower_mul, dividedPower_three_eq_zero, smul_zero]
  have hz4 := dividedPower_eq_zero m i 4 (by omega)
  interval_cases d
  · simp only [Nat.cast_one, one_mul] at h1
    simp only [CoefficientIdentity, curveProductCoefficient, hu]
    change a • dividedPower m i 1 + coordinateOperator m (Sum.inl j) * dividedPower m i 1 =
      dividedPower m i 1 * coordinateOperator m (Sum.inl j)
    rw [← h1]
    ext x y
    simp only [Matrix.add_apply, sub_eq_add_neg, Matrix.neg_apply, CharTwo.neg_eq]
    rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  · simp only [Nat.cast_ofNat, Int.cast_mul, Int.cast_ofNat,
      CharTwo.two_eq_zero, zero_mul, zero_smul, sub_eq_zero] at h2
    simp only [CoefficientIdentity, curveProductCoefficient, hu, hv, Matrix.smul_mul,
      hEE, smul_zero, zero_add, h2]
  · simp only [CoefficientIdentity, curveProductCoefficient, hu, hv,
      columnImage_three_eq_zero, dividedPower_three_eq_zero, Matrix.smul_mul,
      hEB, smul_zero, zero_mul, mul_zero, add_zero]
  · simp only [CoefficientIdentity, curveProductCoefficient, hu, hv,
      columnImage_three_eq_zero, dividedPower_three_eq_zero, hz4,
      zero_mul, mul_zero, add_zero]


end
end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple

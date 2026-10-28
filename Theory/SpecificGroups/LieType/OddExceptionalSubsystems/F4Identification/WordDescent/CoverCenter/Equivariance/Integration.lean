module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.LinearExtension

/-!
# Integrating quadratic adjoint operators over the integers

Suppose `E² = 2B`, `BE = 0`, and an integral linear map satisfies
`D(Ev) = E D(v) - D(v) E`. Its four polynomial coefficient identities imply
`D(X(t)v) X(t) = X(t) D(v)` for `X(t) = 1 + tE + t²B` after specialization
to any commutative ring. In particular, characteristic three is included.

The quadratic identity follows by cancelling 2 over the integers. Applying
it to `Ev`, and combining it with its right product by `E`, gives three
times the cubic identity. Cancelling 3 integrally proves that identity;
applying it once more to `Ev` gives the quartic identity. Thus no cancellation
in the eventual coefficient ring, and no injectivity of `D`, is required.

This is the divided-power argument for the Geck root curves in
`IntegralGeckConstruction`, used for the adjoint Chevalley construction of
GLS3 §§2.2–2.6. The simple-operator commutator identities are separate inputs.
-/

public section

open scoped Matrix
open ReeF4.WordRelations.Faithfulness.Adjoint

namespace TwistedE6.FoldedSubsystem.F4Identification.CoverCenter.EquivarianceIntegration
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
private lemma cancel_int {A B : Matrix n n ℤ} {k : ℤ} (hk : k ≠ 0)
    (h : k • A = k • B) : A = B := by
  ext i j
  exact mul_left_cancel₀ hk (congrFun (congrFun h i) j)

/-- Infinitesimal intertwining on an integral quadratic nilpotent module forces
all four coefficients of adjoint equivariance. Cancellation occurs over the
integers, before any change of characteristic. -/
lemma quadratic_coefficients
    (D : (n → ℤ) →ₗ[ℤ] Matrix n n ℤ) (E B : Matrix n n ℤ)
    (hEE : E * E = (2 : ℤ) • B) (hBE : B * E = 0)
    (hD : ∀ v, D (E *ᵥ v) = E * D v - D v * E) (v : n → ℤ) :
    (D (E *ᵥ v) + D v * E = E * D v) ∧
    (D (B *ᵥ v) + D (E *ᵥ v) * E + D v * B = B * D v) ∧
    (D (B *ᵥ v) * E + D (E *ᵥ v) * B = 0) ∧
    (D (B *ᵥ v) * B = 0) := by
  have h2 (v : n → ℤ) :
      D (B *ᵥ v) + D (E *ᵥ v) * E + D v * B = B * D v := by
    apply cancel_int (by norm_num : (2 : ℤ) ≠ 0)
    have h := hD (E *ᵥ v)
    rw [Matrix.mulVec_mulVec, hEE, Matrix.smul_mulVec, map_smul] at h
    calc
      _ = (E * D (E *ᵥ v) - D (E *ᵥ v) * E) +
          (2 : ℤ) • (D (E *ᵥ v) * E) + (2 : ℤ) • (D v * B) := by
        rw [smul_add, smul_add, h]
      _ = (2 : ℤ) • (B * D v) := by
        rw [hD]
        simp only [mul_sub, sub_mul, ← mul_assoc, hEE, Matrix.smul_mul]
        noncomm_ring
        simp only [hEE, Matrix.mul_smul]
        module
  have h3 (v : n → ℤ) : D (B *ᵥ v) * E + D (E *ᵥ v) * B = 0 := by
    have ha := h2 (E *ᵥ v)
    rw [Matrix.mulVec_mulVec, hBE, Matrix.zero_mulVec, map_zero,
      Matrix.mulVec_mulVec, hEE, Matrix.smul_mulVec, map_smul,
      zero_add, Matrix.smul_mul] at ha
    have hb := congrArg (fun A => A * E) (h2 v)
    simp only [add_mul, mul_assoc, hEE, hBE, Matrix.mul_smul, mul_zero, add_zero] at hb
    have hc := congrArg (fun A => B * A) (hD v)
    simp only [mul_sub, ← mul_assoc, hBE, zero_mul, zero_sub] at hc
    apply cancel_int (by norm_num : (3 : ℤ) ≠ 0)
    rw [smul_zero]
    calc
      (3 : ℤ) • (D (B *ᵥ v) * E + D (E *ᵥ v) * B) =
          ((2 : ℤ) • (D (B *ᵥ v) * E) + D (E *ᵥ v) * B) +
          (D (B *ᵥ v) * E + (2 : ℤ) • (D (E *ᵥ v) * B)) := by module
      _ = B * D (E *ᵥ v) + B * (D v * E) := by rw [ha, hb]
      _ = 0 := by rw [hc]; simp [mul_assoc]
  refine ⟨by rw [hD]; abel, h2 v, h3 v, ?_⟩
  have h := h3 (E *ᵥ v)
  rw [Matrix.mulVec_mulVec, hBE, Matrix.zero_mulVec, map_zero, zero_mul,
    Matrix.mulVec_mulVec, hEE, Matrix.smul_mulVec, map_smul, zero_add,
    Matrix.smul_mul] at h
  exact cancel_int (by norm_num : (2 : ℤ) ≠ 0) (by simpa only [smul_zero] using h)
end TwistedE6.FoldedSubsystem.F4Identification.CoverCenter.EquivarianceIntegration

namespace TwistedE6.FoldedSubsystem.F4Identification.CoverCenter.EquivarianceIntegration
open ReeF4.WordRelations.Faithfulness
variable {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]

omit [DecidableEq n] in
/-- Linear extension of an integral coordinate family commutes with specialization. -/
lemma map_linearExtension (A : n → Matrix n n ℤ) (v : n → ℤ) :
    (linearExtension A v).map (Int.castRingHom K) =
      linearExtension (fun j => (A j).map (Int.castRingHom K))
        ((Int.castRingHom K) ∘ v) := by
  ext x y
  simp only [linearExtension, LinearMap.coe_mk, AddHom.coe_mk, Matrix.map_apply,
    Matrix.sum_apply, Matrix.smul_apply, Function.comp_apply]
  simp only [smul_eq_mul, map_sum, map_mul]

private lemma map_column (A : n → Matrix n n ℤ) (E : Matrix n n ℤ) (j : n) :
    (linearExtension A (E *ᵥ Pi.single j 1)).map (Int.castRingHom K) =
      linearExtension (fun j => (A j).map (Int.castRingHom K))
        (E.map (Int.castRingHom K) *ᵥ Pi.single j 1) := by
  rw [map_linearExtension, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  rfl

private lemma quadratic_product
    (A U V E B : Matrix n n K) (t : K)
    (h1 : U + A * E = E * A)
    (h2 : V + U * E + A * B = B * A)
    (h3 : V * E + U * B = 0) (h4 : V * B = 0) :
    (A + t • U + t ^ 2 • V) * (1 + t • E + t ^ 2 • B) =
      (1 + t • E + t ^ 2 • B) * A := by
  calc
    _ = A + t • (U + A * E) + t ^ 2 • (V + U * E + A * B) +
        t ^ 3 • (V * E + U * B) + t ^ 4 • (V * B) := by
      simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one]
      module
    _ = _ := by
      rw [h1, h2, h3, h4]
      simp only [add_mul, Matrix.smul_mul, one_mul, smul_zero, add_zero]

/-- Integral infinitesimal intertwining implies equivariance after arbitrary
specialization, including characteristic three. -/
lemma equivariant_of_integral_commutator
    (A : n → Matrix n n ℤ) (E B : Matrix n n ℤ)
    (hEE : E * E = (2 : ℤ) • B) (hBE : B * E = 0)
    (hD : ∀ v, linearExtension A (E *ᵥ v) =
      E * linearExtension A v - linearExtension A v * E)
    (t : K) (g : (Matrix n n K)ˣ)
    (hg : (g : Matrix n n K) =
      1 + t • E.map (Int.castRingHom K) + t ^ 2 • B.map (Int.castRingHom K)) :
    Equivariant (linearExtension (fun j => (A j).map (Int.castRingHom K))) g := by
  let D := linearExtension (fun j => (A j).map (Int.castRingHom K))
  apply (equivariant_iff_basis D g).mpr
  intro j
  obtain ⟨h1, h2, h3, h4⟩ := quadratic_coefficients (linearExtension A) E B hEE hBE hD
    (Pi.single j 1)
  have hc1 := congrArg (fun X : Matrix n n ℤ => X.map (Int.castRingHom K)) h1
  have hc2 := congrArg (fun X : Matrix n n ℤ => X.map (Int.castRingHom K)) h2
  have hc3 := congrArg (fun X : Matrix n n ℤ => X.map (Int.castRingHom K)) h3
  have hc4 := congrArg (fun X : Matrix n n ℤ => X.map (Int.castRingHom K)) h4
  simp only [Matrix.map_add _ (map_add _), Matrix.map_mul, map_column,
    linearExtension_single, Matrix.map_zero _ (map_zero _)] at hc1 hc2 hc3 hc4
  change D (_ *ᵥ Pi.single j 1) * _ = _ * D (Pi.single j 1)
  rw [hg]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, map_add, map_smul,
    D, linearExtension_single]
  exact quadratic_product _ _ _ _ _ t hc1 hc2 hc3 hc4
end TwistedE6.FoldedSubsystem.F4Identification.CoverCenter.EquivarianceIntegration

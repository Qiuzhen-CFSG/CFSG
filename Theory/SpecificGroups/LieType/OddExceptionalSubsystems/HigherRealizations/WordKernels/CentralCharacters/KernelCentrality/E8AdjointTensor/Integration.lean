module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.Transport

/-!
# Integral integration for different source and target dimensions

An integral tensor from one lattice into endomorphisms of another intertwines
quadratic root curves as soon as it intertwines their first operators with
commutators. The source and target divided powers may have different dimensions.
The quadratic, cubic and quartic coefficient identities follow by cancellation
of 2 and 3 over ℤ, before any specialization. Thus the resulting polynomial
identity is valid over every commutative ring, including characteristic three.

This extends the equal-carrier argument in
`F4Identification.WordDescent.CoverCenter.Equivariance.Integration` to the
relative E6-in-E8 tensor. `covariance_of_integral_commutator` is the exact
polynomial covariance used by the `IntegralAdjointData` assembly.
Source: GLS3 §§1.12 and 2.6.2 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open Matrix RootPairing.SimpleGeckGroup
namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor

section Integration
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
private lemma cancel_int {A B : Matrix n n ℤ} {k : ℤ} (hk : k ≠ 0)
    (h : k • A = k • B) : A = B := by
  ext i j
  exact mul_left_cancel₀ hk (congrFun (congrFun h i) j)

omit [DecidableEq m] in
/-- Integral cancellation supplies every coefficient of relative adjoint covariance. -/
lemma relative_quadratic_coefficients
    (J : (m → ℤ) →ₗ[ℤ] Matrix n n ℤ)
    (E B : Matrix m m ℤ) (E' B' : Matrix n n ℤ)
    (hEE : E * E = (2 : ℤ) • B) (hBE : B * E = 0)
    (hEE' : E' * E' = (2 : ℤ) • B') (hBE' : B' * E' = 0)
    (hJ : ∀ v, J (E *ᵥ v) = E' * J v - J v * E') (v : m → ℤ) :
    (J (E *ᵥ v) + J v * E' = E' * J v) ∧
    (J (B *ᵥ v) + J (E *ᵥ v) * E' + J v * B' = B' * J v) ∧
    (J (B *ᵥ v) * E' + J (E *ᵥ v) * B' = 0) ∧
    (J (B *ᵥ v) * B' = 0) := by
  have h2 (v : m → ℤ) :
      J (B *ᵥ v) + J (E *ᵥ v) * E' + J v * B' = B' * J v := by
    apply cancel_int (by norm_num : (2 : ℤ) ≠ 0)
    have h := hJ (E *ᵥ v)
    rw [Matrix.mulVec_mulVec, hEE, Matrix.smul_mulVec, map_smul] at h
    calc
      _ = (E' * J (E *ᵥ v) - J (E *ᵥ v) * E') +
          (2 : ℤ) • (J (E *ᵥ v) * E') + (2 : ℤ) • (J v * B') := by
        rw [smul_add, smul_add, h]
      _ = (2 : ℤ) • (B' * J v) := by
        rw [hJ]
        simp only [mul_sub, sub_mul, ← mul_assoc, hEE', Matrix.smul_mul]
        noncomm_ring
        simp only [hEE', Matrix.mul_smul]
        module
  have h3 (v : m → ℤ) : J (B *ᵥ v) * E' + J (E *ᵥ v) * B' = 0 := by
    have ha := h2 (E *ᵥ v)
    rw [Matrix.mulVec_mulVec, hBE, Matrix.zero_mulVec, map_zero,
      Matrix.mulVec_mulVec, hEE, Matrix.smul_mulVec, map_smul,
      zero_add, Matrix.smul_mul] at ha
    have hb := congrArg (fun A => A * E') (h2 v)
    simp only [add_mul, mul_assoc, hEE', hBE', Matrix.mul_smul, mul_zero, add_zero] at hb
    have hc := congrArg (fun A => B' * A) (hJ v)
    simp only [mul_sub, ← mul_assoc, hBE', zero_mul, zero_sub] at hc
    apply cancel_int (by norm_num : (3 : ℤ) ≠ 0)
    rw [smul_zero]
    calc
      (3 : ℤ) • (J (B *ᵥ v) * E' + J (E *ᵥ v) * B') =
          ((2 : ℤ) • (J (B *ᵥ v) * E') + J (E *ᵥ v) * B') +
          (J (B *ᵥ v) * E' + (2 : ℤ) • (J (E *ᵥ v) * B')) := by module
      _ = B' * J (E *ᵥ v) + B' * (J v * E') := by rw [ha, hb]
      _ = 0 := by rw [hc]; simp [mul_assoc]
  refine ⟨by rw [hJ]; abel, h2 v, h3 v, ?_⟩
  have h := h3 (E *ᵥ v)
  rw [Matrix.mulVec_mulVec, hBE, Matrix.zero_mulVec, map_zero, zero_mul,
    Matrix.mulVec_mulVec, hEE, Matrix.smul_mulVec, map_smul, zero_add,
    Matrix.smul_mul] at h
  exact cancel_int (by norm_num : (2 : ℤ) ≠ 0) (by simpa only [smul_zero] using h)

omit [DecidableEq m] [Fintype n] [DecidableEq n] in
private lemma map_tensor {S : Type*} [CommRing S]
    (T : m → Matrix n n ℤ) (v : m → ℤ) :
    (tensorMap T ℤ v).map (Int.castRingHom S) =
      tensorMap T S (fun j => (v j : S)) := by
  ext x y
  simp only [tensorMap_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, map_mul]
  simp

omit [Fintype n] [DecidableEq n] in
private lemma map_tensor_column {S : Type*} [CommRing S]
    (T : m → Matrix n n ℤ) (E : Matrix m m ℤ) (j : m) :
    (tensorMap T ℤ (E *ᵥ Pi.single j 1)).map (Int.castRingHom S) =
      tensorMap T S (E.map (Int.castRingHom S) *ᵥ Pi.single j 1) := by
  rw [map_tensor, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  rfl

private lemma quadratic_product {S : Type*} [CommRing S]
    (A U V E B : Matrix n n S) (t : S)
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

/-- The integral coefficient identities specialize to arbitrary commutative rings. -/
lemma relative_quadratic_covariance {S : Type*} [CommRing S]
    (T : m → Matrix n n ℤ)
    (E B : Matrix m m ℤ) (E' B' : Matrix n n ℤ)
    (hEE : E * E = (2 : ℤ) • B) (hBE : B * E = 0)
    (hEE' : E' * E' = (2 : ℤ) • B') (hBE' : B' * E' = 0)
    (hT : ∀ v, tensorMap T ℤ (E *ᵥ v) =
      E' * tensorMap T ℤ v - tensorMap T ℤ v * E') (t : S) (j : m) :
    (1 + t • E'.map (Int.castRingHom S) + t ^ 2 • B'.map (Int.castRingHom S)) *
        (T j).map (Int.castRingHom S) =
      tensorMap T S
        ((1 + t • E.map (Int.castRingHom S) + t ^ 2 • B.map (Int.castRingHom S)) *ᵥ
          Pi.single j 1) *
        (1 + t • E'.map (Int.castRingHom S) + t ^ 2 • B'.map (Int.castRingHom S)) := by
  obtain ⟨h1, h2, h3, h4⟩ := relative_quadratic_coefficients
    (tensorMap T ℤ) E B E' B' hEE hBE hEE' hBE' hT (Pi.single j 1)
  have hc1 := congrArg (fun X : Matrix n n ℤ => X.map (Int.castRingHom S)) h1
  have hc2 := congrArg (fun X : Matrix n n ℤ => X.map (Int.castRingHom S)) h2
  have hc3 := congrArg (fun X : Matrix n n ℤ => X.map (Int.castRingHom S)) h3
  have hc4 := congrArg (fun X : Matrix n n ℤ => X.map (Int.castRingHom S)) h4
  simp only [Matrix.map_add _ (map_add _), Matrix.map_mul, map_tensor_column,
    tensorMap_single, Matrix.map_zero _ (map_zero _), Matrix.map_map,
    Function.comp_def] at hc1 hc2 hc3 hc4
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, map_add, map_smul,
    tensorMap_single]
  exact (quadratic_product _ _ _ _ _ t hc1 hc2 hc3 hc4).symm

end Integration
end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor

namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
open Matrix RootPairing.SimpleGeckGroup
variable {m n κ : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Basis commutators extend linearly to the entire source lattice. -/
lemma commutator_of_basis (T : m → Matrix n n ℤ)
    (E : Matrix m m ℤ) (E' : Matrix n n ℤ)
    (h : ∀ j, ∑ k, E k j • T k = E' * T j - T j * E') (v : m → ℤ) :
    tensorMap T ℤ (E *ᵥ v) = E' * tensorMap T ℤ v - tensorMap T ℤ v * E' := by
  have hv : v = ∑ j, v j • Pi.single j 1 := by
    ext i
    simp [Pi.single_apply]
  have hj (j : m) : tensorMap T ℤ (E *ᵥ Pi.single j 1) = E' * T j - T j * E' := by
    simpa [Matrix.mulVec_single_one, tensorMap_apply] using h j
  calc
    _ = ∑ j, v j • tensorMap T ℤ (E *ᵥ Pi.single j 1) := by
      conv_lhs => rw [hv]
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, map_sum, map_smul]
    _ = ∑ j, v j • (E' * T j - T j * E') := by simp only [hj]
    _ = _ := by
      simp [tensorMap_apply, smul_sub, Finset.sum_sub_distrib, Matrix.mul_sum,
        Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- Divided-power convolution integrates basis commutators without division after specialization. -/
lemma covariance_of_integral_commutator
    (A : IntegralCubicFamily κ m) (D : IntegralCubicFamily κ n)
    (T : m → Matrix n n ℤ) (a : κ)
    (hA3 : A.dividedPower a 3 = 0) (hD3 : D.dividedPower a 3 = 0)
    (h : ∀ j, ∑ k, A.dividedPower a 1 k j • T k =
      D.dividedPower a 1 * T j - T j * D.dividedPower a 1)
    {S : Type*} [CommRing S] (t : S) (j : m) :
    D.curve a t * (T j).map (Int.castRingHom S) =
      (∑ k, A.curve a t k j • (T k).map (Int.castRingHom S)) * D.curve a t := by
  have hEE := A.mul a 1 1
  have hEE' := D.mul a 1 1
  have hBE : A.dividedPower a 2 * A.dividedPower a 1 = 0 := by
    rw [A.mul, show 2 + 1 = 3 from rfl, hA3, smul_zero]
  have hBE' : D.dividedPower a 2 * D.dividedPower a 1 = 0 := by
    rw [D.mul, show 2 + 1 = 3 from rfl, hD3, smul_zero]
  have hc := relative_quadratic_covariance T
    (A.dividedPower a 1) (A.dividedPower a 2)
    (D.dividedPower a 1) (D.dividedPower a 2)
    (by simpa [two_smul] using hEE) hBE
    (by simpa [two_smul] using hEE') hBE'
    (commutator_of_basis T _ _ h) t j
  simpa only [IntegralCubicFamily.curve, IntegralCubicFamily.coefficient, hA3, hD3,
    Matrix.map_zero _ (map_zero _), smul_zero, add_zero, Matrix.mulVec_single_one,
    tensorMap_apply, Matrix.col_apply] using hc

end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor

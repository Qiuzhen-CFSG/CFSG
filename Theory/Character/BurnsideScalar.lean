module

public import Theory.Character.FiniteOrderTrace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Burnside's scalar-or-zero criterion

A finite-order complex operator whose trace divided by its dimension is an
algebraic integer either has zero trace or is scalar.

The eigenvalues generate a number field. Every complex embedding sends them to
roots of unity, so the normalized trace has all conjugates in the closed unit
disk. Kronecker's theorem makes a nonzero normalized trace a root of unity.
Rescaling by its inverse gives a finite-order operator with trace equal to its
dimension, hence the identity by the finite-order trace criterion.

Source: Brauer–Tuan, *On simple groups of finite order I* (1945), proof of
Lemma 2, pp. 763–764, citing Burnside, p. 322, Theorem I.
-/

noncomputable section
open scoped BigOperators

/-- Burnside's criterion: an integral normalized trace of a finite-order
complex endomorphism is either zero or the scalar by which the operator acts. -/
public theorem finite_order_end_trace_eq_zero_or_scalar_of_isIntegral
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {k : ℕ} (hk : k ≠ 0) (hf : f ^ k = 1)
    (hi : IsIntegral ℤ (LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ))) :
    LinearMap.trace ℂ V f = 0 ∨ ∃ z : ℂ, f = z • 1 := by
  classical
  by_cases ht : LinearMap.trace ℂ V f = 0
  · exact Or.inl ht
  right
  have hd : Module.finrank ℂ V ≠ 0 := by
    intro h
    have hb := finite_order_end_norm_trace_le_finrank f hk hf
    rw [h, Nat.cast_zero] at hb
    exact ht (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))
  have hdc : (Module.finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  let m : f.Eigenvalues → ℕ := fun μ => Module.finrank ℂ (f.eigenspace (μ : ℂ))
  have htrace : LinearMap.trace ℂ V f = ∑ μ : f.Eigenvalues, (μ : ℂ) * (m μ : ℂ) := by
    simpa [m] using Representation.trace_pow_eq_sum_eigenvalues (f := f) (k := 1) hk hf
  have hdim : (Module.finrank ℂ V : ℝ) = ∑ μ : f.Eigenvalues, (m μ : ℝ) := by
    have h := Representation.trace_pow_eq_sum_eigenvalues (f := f) (k := 0) hk hf
    simpa [m] using congrArg Complex.re h
  let S : Set ℂ := Set.range (fun μ : f.Eigenvalues => (μ : ℂ))
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ S
  have hroot (μ : f.Eigenvalues) : (μ : ℂ) ^ k = 1 :=
    Representation.eigenvalue_pow_eq_one_of_pow_eq_one hf μ.property
  let : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin (by
    rintro x ⟨μ, rfl⟩
    exact IsIntegral.of_pow (Nat.pos_of_ne_zero hk) (by rw [hroot]; exact isIntegral_one))
  let : NumberField K := NumberField.of_module_finite ℚ K
  let e : f.Eigenvalues → K := fun μ => ⟨μ, IntermediateField.subset_adjoin ℚ S ⟨μ, rfl⟩⟩
  have he (μ : f.Eigenvalues) : e μ ^ k = 1 := by
    apply Subtype.ext
    exact hroot μ
  let a : K := (∑ μ : f.Eigenvalues, e μ * (m μ : K)) / (Module.finrank ℂ V : K)
  have ha : (a : ℂ) = LinearMap.trace ℂ V f / (Module.finrank ℂ V : ℂ) := by
    simp [a, htrace, e]
  have ha0 : a ≠ 0 := by
    intro h
    have h' := congrArg (fun x : K => (x : ℂ)) h
    rw [ha] at h'
    exact ht ((div_eq_zero_iff.mp h').resolve_right hdc)
  have hai : IsIntegral ℤ a := by
    apply (isIntegral_algHom_iff (K.val.restrictScalars ℤ) Subtype.val_injective).mp
    change IsIntegral ℤ (a : ℂ)
    rw [ha]
    exact hi
  have hab (φ : K →+* ℂ) : ‖φ a‖ ≤ 1 := by
    have heφ (μ : f.Eigenvalues) : ‖φ (e μ)‖ = 1 := by
      apply Complex.norm_eq_one_of_pow_eq_one (n := k) _ hk
      rw [← map_pow, he, map_one]
    have hn : ‖∑ μ : f.Eigenvalues, φ (e μ) * (m μ : ℂ)‖ ≤ (Module.finrank ℂ V : ℝ) := by
      rw [hdim]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro μ _
      simp [heφ]
    dsimp [a]
    simp only [map_div₀, map_sum, map_mul, map_natCast, norm_div, Complex.norm_natCast]
    exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hd)).mpr hn
  obtain ⟨l, hl, hal⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ ha0 hai hab
  let z : ℂ := a
  have hz : z ^ l = 1 := by
    dsimp [z]
    exact_mod_cast hal
  have hz0 : z ≠ 0 := by
    dsimp [z]
    exact_mod_cast ha0
  have hzt : z * (Module.finrank ℂ V : ℂ) = LinearMap.trace ℂ V f := by
    dsimp [z]
    rw [ha, div_mul_cancel₀ _ hdc]
  have hfpow : (z⁻¹ • f) ^ (k * l) = 1 := by
    rw [smul_pow, pow_mul f, hf, one_pow, inv_pow, Nat.mul_comm k l, pow_mul z, hz]
    simp
  have hftrace : LinearMap.trace ℂ V (z⁻¹ • f) = (Module.finrank ℂ V : ℂ) := by
    rw [map_smul, ← hzt]
    simp [smul_eq_mul, hz0]
  have hid := finite_order_end_eq_one_of_trace_eq_finrank (z⁻¹ • f)
    (Nat.mul_ne_zero hk (Nat.ne_of_gt hl)) hfpow hftrace
  refine ⟨z, ?_⟩
  have h := congrArg (fun g : Module.End ℂ V => z • g) hid
  simpa [smul_smul, hz0] using h

/-- The coordinate-space form of Burnside's scalar-or-zero criterion. -/
public theorem burnside_scalar_or_zero
    (n : ℕ) (f : Module.End ℂ (Fin n → ℂ)) (k : ℕ)
    (hk : k ≠ 0) (hf : f ^ k = 1)
    (hi : IsIntegral ℤ (LinearMap.trace ℂ (Fin n → ℂ) f / (n : ℂ))) :
    LinearMap.trace ℂ (Fin n → ℂ) f = 0 ∨ ∃ z : ℂ, f = z • 1 := by
  apply finite_order_end_trace_eq_zero_or_scalar_of_isIntegral f hk hf
  simpa using hi

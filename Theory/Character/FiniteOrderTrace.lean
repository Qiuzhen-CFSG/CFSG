module
public import Theory.Character.CharacterValues
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Integer traces at prime order

A finite-order complex endomorphism has trace bounded by its dimension, with
trace equal to the dimension only for the identity. For prime order, an integer
trace is congruent to the dimension modulo the prime, by reduction modulo a
primitive root minus one. In dimension one less than the prime these facts
force every nonidentity operator with integer trace to have trace minus one.

The equality argument is extracted from the proof of the character-kernel
criterion in BenderGlauberman.Section3.Lemma36. The congruence uses the
cyclotomic argument of Peterfalvi (1.10).
-/

noncomputable section
open scoped BigOperators

/-- A finite-order linear endomorphism whose trace equals the dimension is the
identity. -/
public theorem finite_order_end_eq_one_of_trace_eq_finrank
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0) (hpow : f ^ n = 1)
    (htrace : LinearMap.trace ℂ V f = (Module.finrank ℂ V : ℂ)) :
    f = 1 := by
  classical
  let m : f.Eigenvalues → ℝ :=
    fun μ => (Module.finrank ℂ (f.eigenspace (μ : ℂ)) : ℝ)
  have htrace_one :
      LinearMap.trace ℂ V f =
        ∑ μ : f.Eigenvalues, (μ : ℂ) * (m μ : ℂ) := by
    simpa [m] using
      (Representation.trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 1) hn hpow)
  have htrace_zero :
      (Module.finrank ℂ V : ℂ) =
        ∑ μ : f.Eigenvalues, (m μ : ℂ) := by
    have h0 :=
      Representation.trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 0) hn hpow
    simpa [m, LinearMap.trace_id] using h0
  have hsum_complex :
      ∑ μ : f.Eigenvalues, (μ : ℂ) * (m μ : ℂ) =
        ∑ μ : f.Eigenvalues, (1 : ℂ) * (m μ : ℂ) := by
    rw [← htrace_one, htrace, htrace_zero]
    simp
  have hsum_real :
      ∑ μ : f.Eigenvalues, (μ : ℂ).re * m μ =
        ∑ μ : f.Eigenvalues, (1 : ℝ) * m μ := by
    have h := congrArg Complex.re hsum_complex
    simpa [Complex.re_sum, Complex.re_mul_ofReal] using h
  have hle :
      ∀ μ ∈ (Finset.univ : Finset f.Eigenvalues),
        (μ : ℂ).re * m μ ≤ (1 : ℝ) * m μ := by
    intro μ hμ
    have hμpow : (μ : ℂ) ^ n = 1 :=
      Representation.eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property
    have hnorm : ‖(μ : ℂ)‖ = 1 := by
      have hpowAbs : ‖(μ : ℂ)‖ ^ n = (1 : ℝ) := by
        simpa [hμpow] using (norm_pow (μ : ℂ) n).symm
      have habs_pow : |(‖(μ : ℂ)‖ : ℝ) ^ n| = 1 := by
        rw [hpowAbs, abs_one]
      have habs : |(‖(μ : ℂ)‖ : ℝ)| = 1 :=
        (abs_pow_eq_one (‖(μ : ℂ)‖ : ℝ) hn).mp habs_pow
      simpa [abs_of_nonneg (norm_nonneg (μ : ℂ))] using habs
    have hre_le : (μ : ℂ).re ≤ 1 := by
      simpa [hnorm] using Complex.re_le_norm (μ : ℂ)
    exact mul_le_mul_of_nonneg_right hre_le (by positivity : 0 ≤ m μ)
  have heq_each :
      ∀ μ : f.Eigenvalues, (μ : ℂ).re * m μ = (1 : ℝ) * m μ := by
    intro μ
    exact (Finset.sum_eq_sum_iff_of_le hle).mp (by simpa using hsum_real) μ
      (Finset.mem_univ μ)
  have heigen_eq_one : ∀ μ : f.Eigenvalues, (μ : ℂ) = 1 := by
    intro μ
    have hpos_nat : 0 < Module.finrank ℂ (f.eigenspace (μ : ℂ)) := by
      have hμ : f.HasEigenvalue (μ : ℂ) :=
        Module.End.hasEigenvalue_of_hasGenEigenvalue μ.property
      rcases hμ.exists_hasEigenvector with ⟨v, hv⟩
      rw [Module.finrank_pos_iff_exists_ne_zero]
      refine ⟨⟨v, ?_⟩, ?_⟩
      · rw [Module.End.mem_eigenspace_iff]
        exact hv.apply_eq_smul
      · intro hzero
        have hvzero : v = 0 := by
          simpa using congrArg Subtype.val hzero
        exact hv.2 hvzero
    have hpos : 0 < m μ := by
      dsimp [m]
      exact_mod_cast hpos_nat
    have hre_eq : (μ : ℂ).re = 1 := by
      have h := heq_each μ
      nlinarith
    have hμpow : (μ : ℂ) ^ n = 1 :=
      Representation.eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property
    have hnorm : ‖(μ : ℂ)‖ = 1 := by
      have hpowAbs : ‖(μ : ℂ)‖ ^ n = (1 : ℝ) := by
        simpa [hμpow] using (norm_pow (μ : ℂ) n).symm
      have habs_pow : |(‖(μ : ℂ)‖ : ℝ) ^ n| = 1 := by
        rw [hpowAbs, abs_one]
      have habs : |(‖(μ : ℂ)‖ : ℝ)| = 1 :=
        (abs_pow_eq_one (‖(μ : ℂ)‖ : ℝ) hn).mp habs_pow
      simpa [abs_of_nonneg (norm_nonneg (μ : ℂ))] using habs
    have hnormSq : (μ : ℂ).re * (μ : ℂ).re + (μ : ℂ).im * (μ : ℂ).im = 1 := by
      have h := Complex.normSq_eq_norm_sq (μ : ℂ)
      rw [Complex.normSq_apply, hnorm] at h
      norm_num at h
      exact h
    have him_sq : (μ : ℂ).im * (μ : ℂ).im = 0 := by
      nlinarith
    have him : (μ : ℂ).im = 0 := mul_self_eq_zero.mp him_sq
    exact Complex.ext (by simp [hre_eq]) (by simp [him])
  have htop :
      f.eigenspace (1 : ℂ) = ⊤ := by
    have hsemi : f.IsSemisimple :=
      Representation.end_isSemisimple_of_pow_eq_one f hn hpow
    have hiSup :=
      Representation.eigenspace_iSup_eq_top_over_eigenvalues (f := f) hsemi
    apply top_unique
    rw [← hiSup]
    refine iSup_le ?_
    intro μ
    simp [heigen_eq_one μ]
  ext v
  have hv : v ∈ f.eigenspace (1 : ℂ) := by
    rw [htop]
    exact Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at hv
  simpa using hv

/-- The trace of a finite-order complex operator has absolute value at most
its dimension. -/
public theorem finite_order_end_norm_trace_le_finrank
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0) (hpow : f ^ n = 1) :
    ‖LinearMap.trace ℂ V f‖ ≤ Module.finrank ℂ V := by
  classical
  have hsum : (Module.finrank ℂ V : ℝ) =
      ∑ μ : f.Eigenvalues, (Module.finrank ℂ (f.eigenspace (μ : ℂ)) : ℝ) := by
    have h := Representation.trace_pow_eq_sum_eigenvalues (f := f) (k := 0) hn hpow
    have hr := congrArg Complex.re h
    simpa using hr
  have ht := Representation.trace_pow_eq_sum_eigenvalues (f := f) (k := 1) hn hpow
  simp only [pow_one] at ht
  rw [ht, hsum]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro μ _
  have hnorm : ‖(μ : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one
    (Representation.eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property) hn
  rw [norm_mul, hnorm]
  simp

/-- An integer trace at prime order is congruent to the dimension modulo
the prime. -/
public theorem prime_dvd_integer_trace_sub_finrank
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {p : ℕ} (hp : p.Prime) (hpow : f ^ p = 1)
    (a : ℤ) (ha : LinearMap.trace ℂ V f = (a : ℂ)) :
    (p : ℤ) ∣ a - (Module.finrank ℂ V : ℤ) := by
  let ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hξ : IsPrimitiveRoot ξ p := Complex.isPrimitiveRoot_exp p hp.ne_zero
  have hξmem := eta_mem_cyclotomicOrder ξ
  have hξint : IsIntegral ℤ ξ := by
    refine ⟨Polynomial.X ^ p - 1, Polynomial.monic_X_pow_sub_C (1 : ℤ) hp.ne_zero, ?_⟩
    simp [hξ.pow_eq_one]
  obtain ⟨hmul, hmem, hcong⟩ := finite_order_commuting_trace_mul_congruent
    hξ hp.ne_zero hξ hp.ne_zero (dvd_refl p) hξmem hp.ne_zero hpow
    (show (1 : Module.End ℂ V) ^ p = 1 by simp) (by simp)
  apply prime_dvd_int_of_congruent_zero_mod_one_sub hp hξ hξint hξmem
    (a - (Module.finrank ℂ V : ℤ))
  change _ ∈ Ideal.span _ at hcong ⊢
  convert hcong using 1
  ext
  simp [ha]

/-- In dimension `p - 1`, a nonidentity operator of prime order whose trace
is an integer has trace `-1`. -/
public theorem prime_order_integer_trace_eq_neg_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {p : ℕ} (hp : p.Prime) (hpow : f ^ p = 1)
    (hdim : Module.finrank ℂ V = p - 1) (hne : f ≠ 1)
    (hint : ∃ a : ℤ, LinearMap.trace ℂ V f = (a : ℂ)) :
    LinearMap.trace ℂ V f = -1 := by
  obtain ⟨a, ha⟩ := hint
  have habs : |(a : ℝ)| ≤ (Module.finrank ℂ V : ℝ) := by
    calc
      |(a : ℝ)| = |(LinearMap.trace ℂ V f).re| := by rw [ha]; simp
      _ ≤ ‖LinearMap.trace ℂ V f‖ := Complex.abs_re_le_norm _
      _ ≤ Module.finrank ℂ V := finite_order_end_norm_trace_le_finrank f hp.ne_zero hpow
  have hlo : -(Module.finrank ℂ V : ℤ) ≤ a := by
    exact_mod_cast (abs_le.mp habs).1
  have hhi : a ≤ (Module.finrank ℂ V : ℤ) := by
    exact_mod_cast (abs_le.mp habs).2
  obtain ⟨k, hk⟩ := prime_dvd_integer_trace_sub_finrank f hp hpow a ha
  have hpz : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hdimz : (Module.finrank ℂ V : ℤ) = (p : ℤ) - 1 := by
    rw [hdim, Int.natCast_sub hp.one_le]; norm_num
  have hklo : -1 ≤ k := by nlinarith only [hlo, hk, hpz, hdimz]
  have hkhi : k ≤ 0 := by nlinarith only [hhi, hk, hpz]
  interval_cases k
  · have ha' : a = -1 := by nlinarith only [hk, hdimz]
    simpa [ha'] using ha
  · have ha' : a = (Module.finrank ℂ V : ℤ) := by nlinarith only [hk]
    exfalso
    apply hne
    apply finite_order_end_eq_one_of_trace_eq_finrank f hp.ne_zero hpow
    simpa [ha'] using ha

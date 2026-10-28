module

public import Theory.Character.FiniteOrderTrace
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Schur's prime-power trace spacing lemma

The eigenvalues of a prime-power-order complex operator are powers of a fixed
primitive root. Their multiplicities give a polynomial with natural
coefficients whose evaluation at that root is the trace. If this trace is
rational, subtracting it gives a multiple of the cyclotomic polynomial.
Comparing coefficients and evaluating at one yields a natural number k with
trace equal to dimension minus p times k, and (p - 1) * k at most the dimension.
For a nonidentity operator, the finite-order trace criterion gives k > 0.

Thus rationality of the trace itself suffices; rationality of all power traces
is supplied as a convenient corollary. No rational realization is assumed.

Source: I. Schur, *Über eine Klasse von endlichen Gruppen linearen
Substitutionen* (1905), pp. 77–91; application in Lyons, §5, p. 386.
-/

noncomputable section
open Polynomial
open scoped BigOperators

private lemma pp_block_coeff {p a : ℕ} (hp : p.Prime) (Q : ℚ[X])
    (hQ : Q.natDegree < p ^ a) {r : ℕ} (hr : r < p ^ a) :
    ((cyclotomic (p ^ (a + 1)) ℚ) * Q).coeff (r + p ^ a) = Q.coeff r := by
  rw [cyclotomic_prime_pow_eq_geom_sum hp, Finset.sum_mul, finsetSum_coeff]
  simp_rw [← pow_mul, coeff_X_pow_mul']
  rw [Finset.sum_eq_single 1]
  · simp
  · intro i _ hi
    by_cases hiz : i = 0
    · subst i
      simp only [mul_zero, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
    · have hi2 : 2 ≤ i := by omega
      have hbig : r + p ^ a < p ^ a * i := by nlinarith
      simp [Nat.not_le.mpr hbig]
  · simp [hp.one_lt]

private lemma pp_quotient_degree {p a : ℕ} (hp : p.Prime) {R Q : ℚ[X]}
    (hR : R.natDegree < p ^ (a + 1))
    (heq : R = cyclotomic (p ^ (a + 1)) ℚ * Q) : Q.natDegree < p ^ a := by
  by_cases hQ : Q = 0
  · simp [hQ, pow_pos hp.pos]
  have hc := (cyclotomic.monic (p ^ (a + 1)) ℚ).natDegree_mul' hQ
  rw [← heq, natDegree_cyclotomic, Nat.totient_prime_pow hp (Nat.succ_pos a),
    Nat.add_one_sub_one] at hc
  rw [pow_succ] at hR
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
  nlinarith

private lemma pp_rational_eval {p a : ℕ} (hp : p.Prime) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (p ^ (a + 1))) (P : ℕ[X])
    (hP : P.natDegree < p ^ (a + 1)) (t : ℚ)
    (ht : P.eval₂ (Nat.castRingHom ℂ) ζ = (t : ℂ)) :
    ∃ k : ℕ, (p - 1) * k ≤ P.eval 1 ∧
      (t : ℂ) = (↑(P.eval 1) : ℂ) - (p : ℂ) * k := by
  classical
  let R : ℚ[X] := P.map (Nat.castRingHom ℚ) - C t
  have hRroot : aeval ζ R = 0 := by
    simp only [R, map_sub, aeval_def, eval₂_map]
    have hc : (algebraMap ℚ ℂ).comp (Nat.castRingHom ℚ) = Nat.castRingHom ℂ := by
      ext; simp
    rw [hc]
    simpa using sub_eq_zero.mpr ht
  have hdiv : cyclotomic (p ^ (a + 1)) ℚ ∣ R := by
    rw [cyclotomic_eq_minpoly_rat hζ (pow_pos hp.pos _)]
    exact minpoly.dvd ℚ ζ hRroot
  obtain ⟨Q, hQ⟩ := hdiv
  have hR : R.natDegree < p ^ (a + 1) := by
    apply (natDegree_sub_le _ _).trans_lt
    exact max_lt (natDegree_map_le.trans_lt hP) (by simp [pow_pos hp.pos])
  have hdeg := pp_quotient_degree hp hR hQ
  have hcoeff (r : ℕ) (hr : r < p ^ a) :
      Q.coeff r = (P.coeff (r + p ^ a) : ℚ) := by
    have h := pp_block_coeff hp Q hdeg hr
    rw [← hQ] at h
    simpa [R, coeff_sub, coeff_C, hp.ne_zero] using h.symm
  let k : ℕ := ∑ r ∈ Finset.range (p ^ a), P.coeff (r + p ^ a)
  have hevalQ : Q.eval 1 = (k : ℚ) := by
    rw [eval_eq_sum_range' hdeg]
    simp only [one_pow, mul_one]
    simp only [k, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun r hr => hcoeff r (Finset.mem_range.mp hr))
  have heval : (↑(P.eval 1) : ℚ) - t = (p : ℚ) * k := by
    have : Fact p.Prime := ⟨hp⟩
    have h := congrArg (eval (1 : ℚ)) hQ
    simpa [R, eval_map, eval₂_at_apply, eval_one_cyclotomic_prime_pow, hevalQ] using h
  have hzero : (P.coeff 0 : ℚ) - t = Q.coeff 0 := by
    have h := congrArg (fun F : ℚ[X] => F.coeff 0) hQ
    have hn : 1 < p ^ (a + 1) := one_lt_pow₀ hp.one_lt (by omega)
    simpa [R, mul_coeff_zero, cyclotomic_coeff_zero ℚ hn] using h
  have hQzero_le : Q.coeff 0 ≤ (k : ℚ) := by
    rw [hcoeff 0 (pow_pos hp.pos a)]
    exact_mod_cast (Finset.single_le_sum
      (fun r (_ : r ∈ Finset.range (p ^ a)) => Nat.zero_le (P.coeff (r + p ^ a)))
      (show 0 ∈ Finset.range (p ^ a) by simp [pow_pos hp.pos]) :
      P.coeff (0 + p ^ a) ≤ k)
  have hPzero : (0 : ℚ) ≤ P.coeff 0 := Nat.cast_nonneg _
  refine ⟨k, ?_, ?_⟩
  · have hpcast : (↑(p - 1) : ℚ) = (p : ℚ) - 1 := by
      exact Nat.cast_sub hp.one_le
    have hbound : (↑((p - 1) * k) : ℚ) ≤ (↑(P.eval 1) : ℚ) := by
      push_cast
      rw [hpcast]
      nlinarith
    exact_mod_cast hbound
  · have h : t = (↑(P.eval 1) : ℚ) - (p : ℚ) * k := by linarith [heval]
    exact_mod_cast h

private lemma pp_trace_polynomial
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0) (hf : f ^ n = 1)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    ∃ P : ℕ[X], P.natDegree < n ∧ P.eval 1 = Module.finrank ℂ V ∧
      P.eval₂ (Nat.castRingHom ℂ) ζ = LinearMap.trace ℂ V f := by
  classical
  let : NeZero n := ⟨hn⟩
  have he (μ : f.Eigenvalues) : ∃ i < n, ζ ^ i = (μ : ℂ) :=
    hζ.eq_pow_of_pow_eq_one
      (Representation.eigenvalue_pow_eq_one_of_pow_eq_one hf μ.property)
  choose e he heq using he
  let m (μ : f.Eigenvalues) := Module.finrank ℂ (f.eigenspace (μ : ℂ))
  let P : ℕ[X] := ∑ μ : f.Eigenvalues, monomial (e μ) (m μ)
  refine ⟨P, ?_, ?_, ?_⟩
  · have hdegree : P.degree < (n : WithBot ℕ) := by
      apply (degree_sum_le _ _).trans_lt
      rw [Finset.sup_lt_iff (by simp)]
      intro μ _
      exact (degree_monomial_le _ _).trans_lt (by exact_mod_cast he μ)
    by_cases hP : P = 0
    · simp [hP, Nat.pos_of_ne_zero hn]
    · exact (natDegree_lt_iff_degree_lt hP).mpr hdegree
  · have h := Representation.trace_pow_eq_sum_eigenvalues (f := f) (k := 0) hn hf
    have hsum : (Module.finrank ℂ V : ℂ) = ∑ μ : f.Eigenvalues, (m μ : ℂ) := by
      simpa [m] using h
    dsimp [P]
    simp only [eval_finsetSum, eval_monomial, one_pow, mul_one]
    exact_mod_cast hsum.symm
  · dsimp [P]
    simp only [eval₂_finsetSum, eval₂_monomial, heq]
    have h := Representation.trace_pow_eq_sum_eigenvalues (f := f) (k := 1) hn hf
    simpa [m, mul_comm] using h.symm

/-- A nonidentity complex operator of prime-power order with rational trace
has trace in Schur's evenly spaced list, of length finrank / (p - 1). -/
public theorem prime_power_trace_spacing_of_rational
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {p a : ℕ} (hp : p.Prime) (hpow : f ^ (p ^ a) = 1)
    (hne : f ≠ 1) (hrat : ∃ q : ℚ, LinearMap.trace ℂ V f = (q : ℂ)) :
    ∃ j : ℕ, j < Module.finrank ℂ V / (p - 1) ∧
      LinearMap.trace ℂ V f = (Module.finrank ℂ V : ℂ) -
        (p : ℂ) * (j + 1) := by
  classical
  cases a with
  | zero => exact (hne (by simpa using hpow)).elim
  | succ a =>
    let n := p ^ (a + 1)
    let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
    have hn : n ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn
    obtain ⟨P, hPdeg, hPone, hPtrace⟩ := pp_trace_polynomial f hn hpow hζ
    obtain ⟨q, hq⟩ := hrat
    have hq' : P.eval₂ (Nat.castRingHom ℂ) ζ = (q : ℂ) := hPtrace.trans hq
    obtain ⟨k, hkdim, hk⟩ := pp_rational_eval hp hζ P hPdeg q hq'
    rw [hPone] at hkdim hk
    have htrace : LinearMap.trace ℂ V f =
        (Module.finrank ℂ V : ℂ) - (p : ℂ) * k := hq.trans hk
    have hkpos : 0 < k := by
      by_contra hk0
      have hkz : k = 0 := Nat.eq_zero_of_not_pos hk0
      have htr : LinearMap.trace ℂ V f = (Module.finrank ℂ V : ℂ) := by
        simpa [hkz] using htrace
      exact hne (finite_order_end_eq_one_of_trace_eq_finrank f hn hpow htr)
    refine ⟨k - 1, ?_, ?_⟩
    · have hkle : k ≤ Module.finrank ℂ V / (p - 1) := by
        apply (Nat.le_div_iff_mul_le (by have := hp.two_le; omega : 0 < p - 1)).mpr
        simpa [Nat.mul_comm] using hkdim
      omega
    · have hkcast : ((k - 1 : ℕ) : ℂ) + 1 = (k : ℂ) := by
        exact_mod_cast Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hkpos))
      simpa only [hkcast] using htrace

/-- Rational power traces of a nonidentity prime-power-order operator have
Schur's spacing and range. -/
public theorem prime_power_rational_trace_spacing
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {p a : ℕ} (hp : p.Prime) (hpow : f ^ (p ^ a) = 1)
    (hne : f ≠ 1)
    (hrat : ∀ i : ℕ, ∃ q : ℚ,
      LinearMap.trace ℂ V (f ^ i) = (q : ℂ)) :
    ∃ j : ℕ, j < Module.finrank ℂ V / (p - 1) ∧
      LinearMap.trace ℂ V f = (Module.finrank ℂ V : ℂ) -
        (p : ℂ) * (j + 1) := by
  apply prime_power_trace_spacing_of_rational f hp hpow hne
  simpa only [pow_one] using hrat 1

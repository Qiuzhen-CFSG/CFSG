module

public import Theory.Representation.IntegralPermutationTrace
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.Algebra.Operations

/-!
# Integral spectral projectors and fixed-point-free permutation traces

For a finite-order operator over a domain containing the required roots of
unity, with its order invertible, finite Fourier averages give commuting
idempotent spectral projectors whose sum is the identity. This construction
works over the integral coefficient ring itself.

If a prime-power permutation has no fixed basis vectors and commutes with both
that operator and an idempotent, its trace against their product is zero.
Apply the integral permutation-summand theorem to each spectral projector
times the given idempotent, then recombine by trace linearity.

The projector construction is the usual finite geometric-sum argument. The
trace application is the mixed form of the Brauer--Suzuki argument cited in
Fong, *Some Sylow subgroups of order 32 and a characterization of U(3,3)*,
J. Algebra 6 (1967), p. 71, equation (6).
-/

public section

open scoped BigOperators
noncomputable section
namespace IntegralSpectral
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

private lemma average_fixed (W : A) {n : ℕ} (hW : W ^ n = 1) (c : R) :
    W * (c • ∑ i ∈ Finset.range n, W ^ i) = c • ∑ i ∈ Finset.range n, W ^ i := by
  have h := mul_geom_sum W n
  rw [hW, sub_self, sub_mul, one_mul, sub_eq_zero] at h
  simpa only [Algebra.mul_smul_comm] using congrArg (fun x : A => c • x) h

private lemma average_idempotent (W : A) {n : ℕ} (hW : W ^ n = 1)
    (c : R) (hc : c * n = 1) :
    IsIdempotentElem (c • ∑ i ∈ Finset.range n, W ^ i) := by
  let E : A := c • ∑ i ∈ Finset.range n, W ^ i
  have hWE : W * E = E := average_fixed W hW c
  have hi (i : ℕ) : W ^ i * E = E := by
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', mul_assoc, ih, hWE]
  change E * E = E
  calc
    E * E = c • ∑ i ∈ Finset.range n, W ^ i * E := by
      simp only [E, Algebra.smul_mul_assoc, Finset.sum_mul]
    _ = c • (n • E) := by simp only [hi, Finset.sum_const, Finset.card_range]
    _ = E := by rw [← Nat.cast_smul_eq_nsmul R, smul_smul, hc, one_smul]

private lemma commute_average (U V : A) (h : Commute V U) (a c : R) (n : ℕ) :
    Commute V (c • ∑ i ∈ Finset.range n, (a • U) ^ i) := by
  apply Commute.smul_right
  apply Commute.sum_right
  intro i hi
  exact (h.smul_right a).pow_right i

private lemma root_sum [IsDomain R] {n : ℕ} {ζ : R}
    (hζ : IsPrimitiveRoot ζ n) {i : ℕ} (hi : i < n) :
    (∑ j ∈ Finset.range n, (ζ ^ j) ^ i) = if i = 0 then (n : R) else 0 := by
  split_ifs with hi0
  · simp [hi0]
  · have hne := hζ.pow_ne_one_of_pos_of_lt hi0 hi
    have hp : (ζ ^ i) ^ n = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hh := mul_geom_sum (ζ ^ i) n
    rw [hp, sub_self] at hh
    have hs : (∑ j ∈ Finset.range n, (ζ ^ i) ^ j) = 0 :=
      (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hne)
    convert hs using 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Integral spectral projectors for an operator killed by a split unit-order polynomial. -/
theorem exists_projectors [IsDomain R] {n : ℕ} (hn : n ≠ 0)
    (ζ : Rˣ) (hζ : IsPrimitiveRoot (ζ : R) n)
    (c : R) (hc : c * n = 1) (U : A) (hU : U ^ n = 1) :
    ∃ E : Fin n → A,
      (∀ j, IsIdempotentElem (E j)) ∧
      (∑ j, E j) = 1 ∧
      (∀ j, U * E j = ((↑(ζ⁻¹) : R) ^ (j : ℕ)) • E j) ∧
      (∀ (V : A), Commute V U → ∀ j, Commute V (E j)) := by
  let E : Fin n → A := fun j => c • ∑ i ∈ Finset.range n, (((ζ : R) ^ (j : ℕ)) • U) ^ i
  have hp (j : Fin n) : ((((ζ : R) ^ (j : ℕ)) • U) ^ n) = 1 := by
    rw [smul_pow, hU, ← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow, one_smul]
  refine ⟨E, fun j => average_idempotent _ (hp j) c hc, ?_, ?_, ?_⟩
  · change (∑ j : Fin n, c • ∑ i ∈ Finset.range n, (((ζ : R) ^ (j : ℕ)) • U) ^ i) = 1
    rw [← Finset.smul_sum, Fin.sum_univ_eq_sum_range
      (fun j : ℕ => ∑ i ∈ Finset.range n, (((ζ : R) ^ j) • U) ^ i), Finset.sum_comm]
    simp_rw [smul_pow, ← Finset.sum_smul]
    have hs : (∑ i ∈ Finset.range n,
        (∑ j ∈ Finset.range n, ((ζ : R) ^ j) ^ i) • U ^ i) = (n : R) • (1 : A) := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro i hi hi0
        rw [root_sum hζ (Finset.mem_range.mp hi), if_neg hi0, zero_smul]
      · simp [Nat.pos_of_ne_zero hn]
    rw [hs, smul_smul, hc, one_smul]
  · intro j
    have hfixed := average_fixed _ (hp j) c
    change (((ζ : R) ^ (j : ℕ)) • U) * E j = E j at hfixed
    rw [Algebra.smul_mul_assoc] at hfixed
    have hh := congrArg (fun x : A => ((↑(ζ⁻¹) : R) ^ (j : ℕ)) • x) hfixed
    simpa only [smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul] using hh
  · intro V hV j
    exact commute_average U V hV _ _ _
end IntegralSpectral

namespace Matrix
variable {R k X : Type*} [CommRing R] [IsDomain R] [Field k]
  [Fintype X] [DecidableEq X]

/-- A fixed-point-free prime-power permutation has zero trace against an
idempotent times a commuting split finite-order operator of invertible order. -/
theorem trace_permMatrix_mul_mul_eq_zero_of_prime {p : ℕ} [Fact p.Prime] [CharP k p]
    (f : R →+* k) (hsurj : Function.Surjective f)
    (hf : ∀ r, f r ≠ 0 → IsUnit r)
    (σ : Equiv.Perm X) {a : ℕ} (hσ : σ ^ (p ^ a) = 1)
    (hfix : ∀ x, σ x ≠ x)
    (U P : Matrix X X R) (hP : IsIdempotentElem P)
    (hTP : Commute (σ.permMatrix R) P) (hUP : Commute U P)
    (hTU : Commute (σ.permMatrix R) U)
    {n : ℕ} (hn : n ≠ 0) (hU : U ^ n = 1)
    (hnunit : IsUnit (n : R)) (ζ : R) (hζ : IsPrimitiveRoot ζ n) :
    trace (σ.permMatrix R * U * P) = 0 := by
  classical
  let root : Rˣ := (hζ.isUnit hn).unit
  have hroot : IsPrimitiveRoot (root : R) n := by
    simpa only [root, IsUnit.unit_spec] using hζ
  let c : R := ↑(hnunit.unit⁻¹)
  have hc : c * n = 1 := by
    rw [← hnunit.unit_spec]
    exact Units.inv_mul hnunit.unit
  obtain ⟨E, hE, hsum, hUE, hcomm⟩ :=
    IntegralSpectral.exists_projectors hn root hroot c hc U hU
  have hzero (j : Fin n) : trace (σ.permMatrix R * (E j * P)) = 0 := by
    have hi : IsIdempotentElem (E j * P) :=
      IsIdempotentElem.mul_of_commute (hcomm P hUP.symm j).symm (hE j) hP
    have ht : Commute (σ.permMatrix R) (E j * P) :=
      (hcomm _ hTU j).mul_right hTP
    have hh := trace_permMatrix_mul_eq_trace_fixed_lift_of_prime f hsurj hf σ hσ
      (E j * P) hi ht (0 : Matrix {x // σ x = x} {x // σ x = x} R)
      (by simp [IsIdempotentElem]) (by ext i; exact (hfix i.val i.property).elim)
    simpa only [trace_zero] using hh
  calc
    trace (σ.permMatrix R * U * P) =
        ∑ j, trace (σ.permMatrix R * (U * E j) * P) := by
      rw [← trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum,
        hsum, mul_one]
    _ = ∑ j : Fin n, ((↑(root⁻¹) : R) ^ (j : ℕ)) •
        trace (σ.permMatrix R * (E j * P)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hUE, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, trace_smul, mul_assoc]
    _ = 0 := by simp only [hzero, smul_zero, Finset.sum_const_zero]

end Matrix

namespace Matrix
variable {R k X : Type*} [CommRing R] [IsDomain R] [Field k] [CharP k 2]
  [Fintype X] [DecidableEq X]

/-- Characteristic-two specialization, retaining the original API. -/
theorem trace_permMatrix_mul_mul_eq_zero
    (f : R →+* k) (hsurj : Function.Surjective f)
    (hf : ∀ r, f r ≠ 0 → IsUnit r)
    (σ : Equiv.Perm X) {a : ℕ} (hσ : σ ^ (2 ^ a) = 1)
    (hfix : ∀ x, σ x ≠ x)
    (U P : Matrix X X R) (hP : IsIdempotentElem P)
    (hTP : Commute (σ.permMatrix R) P) (hUP : Commute U P)
    (hTU : Commute (σ.permMatrix R) U)
    {n : ℕ} (hn : n ≠ 0) (hU : U ^ n = 1)
    (hnunit : IsUnit (n : R)) (ζ : R) (hζ : IsPrimitiveRoot ζ n) :
    trace (σ.permMatrix R * U * P) = 0 := by
  exact trace_permMatrix_mul_mul_eq_zero_of_prime (p := 2) f hsurj hf σ hσ hfix U P hP hTP hUP hTU hn hU hnunit ζ hζ
end Matrix

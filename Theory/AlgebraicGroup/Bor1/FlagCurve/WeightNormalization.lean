module

public import Theory.AlgebraicGroup.Tori.Power
public import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Normalizing the weights of a projective monomial curve

Over an algebraically closed field, a nonzero power map on the units is
surjective. Dividing all occupied nonnegative exponents by their gcd therefore
preserves the literal monomial orbit, without a separability assertion.
Reflection about the maximal exponent preserves gcd one when exponent zero
occurs, so both extreme affine charts admit the normality argument.

These are the arithmetic and point-image identities for the direct torus-curve
proof of Borel, Linear Algebraic Groups, §13.13(3→4).
-/

public noncomputable section

namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {ι : Type v}

/-- Dividing occupied nonnegative weights by their gcd preserves the actual
monomial orbit over an algebraically closed field, including characteristic p. -/
theorem monomial_orbit_range_normalize
    (s : Finset ι) (c : ι → k) (n : ι → ℕ)
    (hc : ∀ i ∉ s, c i = 0) (i₀ : ι) (hi₀ : i₀ ∈ s) (hn₀ : n i₀ ≠ 0) :
    Set.range (fun t : kˣ => fun i => c i * (t : k) ^ n i) =
      Set.range (fun t : kˣ => fun i => c i * (t : k) ^ (n i / s.gcd n)) := by
  classical
  let d := s.gcd n
  have hd : d ≠ 0 := by
    intro h
    exact hn₀ ((Finset.gcd_eq_zero_iff.mp h) i₀ hi₀)
  have hsurj : Function.Surjective (fun t : kˣ => t ^ d) := by
    simpa only [zpow_natCast] using
      (units_zpow_surjective_of_isAlgClosed (k := k) (d : ℤ) (by exact_mod_cast hd))
  have hcoord (t : kˣ) :
      (fun i => c i * (t : k) ^ n i) =
        (fun i => c i * ((t ^ d : kˣ) : k) ^ (n i / d)) := by
    funext i
    by_cases hi : i ∈ s
    · have hdiv : d ∣ n i := Finset.gcd_dvd hi
      rw [Units.val_pow_eq_pow_val, ← pow_mul, Nat.mul_div_cancel' hdiv]
    · simp only [hc i hi, zero_mul]
  have hf : (fun t : kˣ => fun i => c i * (t : k) ^ n i) =
      (fun t : kˣ => fun i => c i * (t : k) ^ (n i / d)) ∘ (fun t => t ^ d) :=
    funext hcoord
  rw [hf, Set.range_comp, hsurj.range_eq, Set.image_univ]

/-- Both extreme affine charts have coprime normalized exponents: reflection
of the exponents around their maximum preserves gcd one when zero occurs. -/
theorem reflected_exponents_gcd_one
    (s : Finset ι) (n : ι → ℕ) (N : ℕ) (i₀ : ι)
    (hi₀ : i₀ ∈ s) (hn₀ : n i₀ = 0) (hN : ∀ i ∈ s, n i ≤ N)
    (hgcd : s.gcd n = 1) : s.gcd (fun i => N - n i) = 1 := by
  let d := s.gcd (fun i => N - n i)
  have hdN : d ∣ N := by
    simpa only [hn₀, Nat.sub_zero] using (Finset.gcd_dvd (f := fun i => N - n i) hi₀)
  have hdn : ∀ i ∈ s, d ∣ n i := by
    intro i hi
    have hh := Nat.dvd_sub hdN (Finset.gcd_dvd (f := fun i => N - n i) hi)
    simpa only [Nat.sub_sub_self (hN i hi)] using hh
  have hh : d ∣ s.gcd n := Finset.dvd_gcd hdn
  rw [hgcd] at hh
  exact Nat.dvd_one.mp hh

end Theory.AlgebraicGroup.Bor1.FlagCurve

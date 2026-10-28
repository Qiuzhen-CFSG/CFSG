module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# Normal monomial charts of a projective torus curve

A normal subalgebra contains an integral element when that element is already
a fraction of its elements. Applying this observation to powers and following
the Euclidean algorithm recovers the power with gcd exponent. Thus a normal
subalgebra of k[t] containing monomials whose exponents have gcd one is all
of k[t]. The final theorem applies this directly to an injective affine-chart
pullback with the actual nonzero coordinate coefficients retained.

This is the characteristic-independent affine normalization step in the direct
monomial-curve proof of Borel, Linear Algebraic Groups, §13.13(3→4). Dividing
weight differences by their gcd is essential: the original torus orbit map
can be inseparable in positive characteristic.
-/

public noncomputable section

namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u v
variable {k : Type u} [Field k]
variable {R : Type v} [CommRing R] [IsDomain R] [Algebra k R]

/-- A normal subalgebra contains every integral element already expressible
as a fraction of two of its elements. -/
theorem normal_mem_of_integral_fraction (A : Subalgebra k R) [IsIntegrallyClosed A]
    (x : R) (hx : IsIntegral A x)
    (a b : A) (hb : (b : R) ≠ 0) (hab : x * (b : R) = (a : R)) : x ∈ A := by
  let K := FractionRing A
  let L := FractionRing R
  let i : A →ₐ[A] L := Algebra.ofId A L
  have hi : Function.Injective i := by
    change Function.Injective ((algebraMap R L) ∘ (Subtype.val : A → R))
    exact (IsFractionRing.injective R L).comp Subtype.val_injective
  let f : K →ₐ[A] L := IsFractionRing.liftAlgHom hi
  let y : K := algebraMap A K a / algebraMap A K b
  have hfa (c : A) : f (algebraMap A K c) = algebraMap R L (c : R) := by
    change (IsFractionRing.lift hi) (algebraMap A K c) = _
    rw [IsFractionRing.lift_algebraMap]
    rfl
  have hfy : f y = algebraMap R L x := by
    rw [map_div₀, hfa, hfa]
    have hbL : algebraMap R L (b : R) ≠ 0 := by
      intro hzero
      exact hb (IsFractionRing.injective R L (hzero.trans (map_zero _).symm))
    apply (div_eq_iff hbL).mpr
    rw [← map_mul, hab]
  have hyl : IsIntegral A (f y) := by
    rw [hfy]
    exact hx.map (IsScalarTower.toAlgHom A R L)
  have hy : IsIntegral A y := (isIntegral_algHom_iff f f.injective).mp hyl
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hy
  have he := congrArg f hc
  rw [hfa, hfy] at he
  have hcx : (c : R) = x := IsFractionRing.injective R L he
  exact hcx ▸ c.property


/-- Normality recovers the power whose exponent is the gcd of two available
powers. The proof is the Euclidean algorithm inside the fraction field. -/
theorem normal_pow_gcd_mem (A : Subalgebra k R) [IsIntegrallyClosed A]
    (x : R) (hx : x ≠ 0) (m n : ℕ) (hm : x ^ m ∈ A) (hn : x ^ n ∈ A) :
    x ^ Nat.gcd m n ∈ A := by
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
    by_cases hm0 : m = 0
    · simpa only [hm0, Nat.gcd_zero_left] using hn
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hxint : IsIntegral A x := IsIntegral.of_pow hmpos
      (show IsIntegral A (x ^ m) from isIntegral_algebraMap (x := (⟨x ^ m, hm⟩ : A)))
    have hb : x ^ (m * (n / m)) ∈ A := by
      rw [pow_mul]
      exact A.pow_mem hm _
    have hmod : x ^ (n % m) ∈ A := by
      apply normal_mem_of_integral_fraction A _ (hxint.pow _) ⟨x ^ n, hn⟩
        ⟨x ^ (m * (n / m)), hb⟩ (pow_ne_zero _ hx)
      change x ^ (n % m) * x ^ (m * (n / m)) = x ^ n
      rw [← pow_add, Nat.mod_add_div]
    rw [Nat.gcd_rec]
    exact ih (n % m) (Nat.mod_lt n hmpos) m hmod hm

/-- The gcd of a finite family of monomial powers belongs to a normal subalgebra. -/
theorem normal_pow_finset_gcd_mem (A : Subalgebra k R) [IsIntegrallyClosed A]
    (x : R) (hx : x ≠ 0) {ι : Type*} (s : Finset ι) (n : ι → ℕ)
    (hn : ∀ i ∈ s, x ^ n i ∈ A) : x ^ s.gcd n ∈ A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.gcd_empty, pow_zero]; exact A.one_mem
  | @insert i s hi ih =>
    rw [Finset.gcd_insert]
    exact normal_pow_gcd_mem A x hx _ _ (hn i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hn j (Finset.mem_insert_of_mem hj)))

/-- A normal polynomial subalgebra containing monomials with coprime total
exponent gcd is the entire polynomial ring. This identifies the affine charts
of a normal projective monomial curve after dividing the weight gcd. -/
theorem normal_polynomial_subalgebra_eq_top
    (A : Subalgebra k (Polynomial k)) [IsIntegrallyClosed A]
    {ι : Type*} (s : Finset ι) (n : ι → ℕ) (hgcd : s.gcd n = 1)
    (hn : ∀ i ∈ s, Polynomial.X ^ n i ∈ A) : A = ⊤ := by
  have hX := normal_pow_finset_gcd_mem A Polynomial.X Polynomial.X_ne_zero s n hn
  rw [hgcd, pow_one] at hX
  apply top_unique
  rw [← Polynomial.adjoin_X]
  apply Algebra.adjoin_le
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  exact hX


/-- Literal affine-chart consumer: a faithful pullback into k[t] is an
isomorphism if the source is normal and its image contains nonzero multiples
of monomials whose exponents have gcd one. -/
theorem normal_polynomial_hom_surjective
    {A : Type*} [CommRing A] [Algebra k A] [IsIntegrallyClosed A]
    (f : A →ₐ[k] Polynomial k) (hf : Function.Injective f)
    {ι : Type*} (s : Finset ι) (n : ι → ℕ) (c : ι → k)
    (hc : ∀ i ∈ s, c i ≠ 0) (hgcd : s.gcd n = 1)
    (hgen : ∀ i ∈ s, Polynomial.C (c i) * Polynomial.X ^ n i ∈ f.range) :
    Function.Surjective f := by
  let : IsIntegrallyClosed f.range :=
    IsIntegrallyClosed.of_equiv (AlgEquiv.ofInjective f hf).toRingEquiv
  have hp : ∀ i ∈ s, Polynomial.X ^ n i ∈ f.range := by
    intro i hi
    have hh := f.range.mul_mem (f.range.algebraMap_mem (c i)⁻¹) (hgen i hi)
    change Polynomial.C (c i)⁻¹ * (Polynomial.C (c i) * Polynomial.X ^ n i) ∈ f.range at hh
    simpa only [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ (hc i hi),
      Polynomial.C_1, one_mul] using hh
  exact (AlgHom.range_eq_top f).mp (normal_polynomial_subalgebra_eq_top f.range s n hgcd hp)

end Theory.AlgebraicGroup.Bor1.FlagCurve

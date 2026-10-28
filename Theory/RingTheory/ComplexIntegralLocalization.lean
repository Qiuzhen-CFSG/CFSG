module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.RootsOfUnity.Minpoly
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Local coefficient rings inside the complex numbers

For every rational prime `p`, there is a local subring of `ℂ` in which `p`
is not a unit, containing every complex number that becomes integral over `ℤ`
after multiplication by an integer prime to `p`. It also contains primitive
roots of unity of every positive order.

Take the integral closure of `ℤ` in `ℂ`, choose a prime lying over `(p)`,
and embed its localization into `ℂ`. The contraction of the prime detects
exactly which natural numbers are inverted. Integrality of roots of unity
then supplies the root witnesses. No Noetherian or discrete valuation
assumption is used.

The algebraic inputs are the lying-over theorem in
`Mathlib.RingTheory.Ideal.GoingUp`, localization at a prime in
`Mathlib.RingTheory.Localization.AtPrime.Basic`, and root-of-unity integrality
in `Mathlib.RingTheory.RootsOfUnity.Minpoly`.
-/

public section

noncomputable section

namespace ComplexIntegralLocalization

private abbrev A := integralClosure ℤ ℂ

private theorem exists_prime (p : ℕ) [Fact p.Prime] :
    ∃ Q : Ideal A, Q.IsPrime ∧
      Q.comap (algebraMap ℤ A) = Ideal.span {(p : ℤ)} := by
  have hp : Nat.Prime p := Fact.out
  have : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
      (by simpa only [Int.prime_iff_natAbs_prime, Int.natAbs_natCast] using hp)
  apply Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective ℤ A)]
  exact bot_le

private def toComplex (Q : Ideal A) [Q.IsPrime] : Localization.AtPrime Q →+* ℂ :=
  IsLocalization.lift (M := Q.primeCompl) (S := Localization.AtPrime Q)
    (g := A.subtype) (by
      intro y
      apply isUnit_iff_ne_zero.mpr
      intro hy
      apply y.2
      have hy0 : y.1 = 0 := Subtype.ext hy
      rw [hy0]
      exact Q.zero_mem)

private theorem toComplex_algebraMap (Q : Ideal A) [Q.IsPrime] (a : A) :
    toComplex Q (algebraMap A _ a) = (a : ℂ) := IsLocalization.lift_eq _ _

private theorem toComplex_injective (Q : Ideal A) [Q.IsPrime] :
    Function.Injective (toComplex Q) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq Q.primeCompl (toComplex Q)).2
  intro x y
  constructor
  · exact congrArg (toComplex Q)
  · intro h
    have hxy : x = y := Subtype.ext (by simpa only [toComplex_algebraMap] using h)
    rw [hxy]

/-- A local subring of `ℂ` containing all coefficients integral away from `p`
and primitive roots of unity of every nonzero order, with `p` a nonunit. -/
theorem exists_subring (p : ℕ) [Fact p.Prime] :
    ∃ S : Subring ℂ, IsLocalRing S ∧ ¬ IsUnit (p : S) ∧
      (∀ z : ℂ, (∃ m : ℕ, ¬ p ∣ m ∧ IsIntegral ℤ ((m : ℂ) * z)) → z ∈ S) ∧
      ∀ n : ℕ, n ≠ 0 → ∃ ζ : S, IsPrimitiveRoot ζ n := by
  obtain ⟨Q, hQ, hQcomap⟩ := exists_prime p
  let : Q.IsPrime := hQ
  let L := Localization.AtPrime Q
  let f := toComplex Q
  let S := f.range
  let e : L ≃+* S := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => toComplex_injective Q (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hcast (m : ℕ) : (m : A) ∈ Q ↔ p ∣ m := by
    change algebraMap ℤ A (m : ℤ) ∈ Q ↔ _
    rw [← Ideal.mem_comap, hQcomap, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]
  have hnotunit : ¬ IsUnit (p : L) := by
    rw [← map_natCast (algebraMap A L), IsLocalization.AtPrime.isUnit_to_map_iff L Q]
    exact fun h => h ((hcast p).2 (dvd_refl p))
  have hmem (z : ℂ) (hz : ∃ m : ℕ, ¬ p ∣ m ∧ IsIntegral ℤ ((m : ℂ) * z)) : z ∈ S := by
    obtain ⟨m, hm, hz⟩ := hz
    have hmQ : (m : A) ∈ Q.primeCompl := fun h => hm ((hcast m).1 h)
    let a : A := ⟨(m : ℂ) * z, hz⟩
    let b : Q.primeCompl := ⟨(m : A), hmQ⟩
    refine ⟨IsLocalization.mk' L a b, ?_⟩
    have h := congrArg f (IsLocalization.mk'_spec L a b)
    simp only [f, L, map_mul, toComplex_algebraMap] at h
    have hm0 : (m : ℂ) ≠ 0 := by
      exact_mod_cast (show m ≠ 0 from fun h => hm (h ▸ dvd_zero p))
    apply mul_right_cancel₀ hm0
    change f (IsLocalization.mk' L a b) * (m : ℂ) = (m : ℂ) * z at h
    simpa only [mul_comm] using h
  refine ⟨S, e.isLocalRing, ?_, hmem, ?_⟩
  · intro h
    apply hnotunit
    simpa only [map_natCast] using h.map e.symm
  · intro n hn
    let ζ := Complex.exp (2 * Real.pi * Complex.I / n)
    have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn
    have hζS : ζ ∈ S := hmem ζ ⟨1, (Fact.out : Nat.Prime p).not_dvd_one,
      by simpa only [Nat.cast_one, one_mul] using hζ.isIntegral (Nat.pos_of_ne_zero hn)⟩
    exact ⟨⟨ζ, hζS⟩, IsPrimitiveRoot.of_map_of_injective (f := S.subtype) hζ
      Subtype.val_injective⟩

end ComplexIntegralLocalization

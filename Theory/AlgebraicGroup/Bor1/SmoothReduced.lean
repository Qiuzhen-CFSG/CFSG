module

public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Theory.AlgebraicGroup.Bor1.EtaleReduced

/-!
Smooth algebras over a field are reduced.  The proof covers a smooth algebra
by standard-smooth principal opens, presents each localization as an etale
algebra over a polynomial ring, and proves that etale algebra reducedness by
embedding into the fraction-field base change.  The latter step is what lets
the public theorem support independent universes for the field and algebra.
-/

universe u v

namespace Theory.AlgebraicGroup.Bor1

open scoped TensorProduct

set_option linter.style.haveILetI false in
private theorem isReduced_of_etale_of_domain
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R]
    [Algebra R S] [Algebra.Etale R S] : IsReduced S := by
  let K := FractionRing R
  letI : Field K := FractionRing.field R
  let T := K ⊗[R] S
  letI : Algebra.Etale K T := Algebra.Etale.baseChange R S K
  letI : IsReduced T := Algebra.FormallyUnramified.isReduced_of_field K T
  apply isReduced_of_injective
    (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := S)).toRingHom
  apply Algebra.TensorProduct.includeRight_injective
  exact IsFractionRing.injective R K

set_option linter.style.haveILetI false in
/-- A smooth algebra over a field is reduced. -/
public theorem isReduced_of_smooth_of_field
    {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] : IsReduced A := by
  obtain ⟨s, hs, hstd⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth K A
  have hredAway (r : A) (hr : r ∈ s) : IsReduced (Localization.Away r) := by
    have hfstd : (algebraMap K (Localization.Away r)).IsStandardSmooth :=
      RingHom.isStandardSmooth_algebraMap.mpr (hstd r hr)
    obtain ⟨n, g, -, hgetale⟩ := hfstd.exists_etale_mvPolynomial
    letI : Algebra (MvPolynomial (Fin n) K) (Localization.Away r) := g.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin n) K) (Localization.Away r) :=
      hgetale.toAlgebra
    exact isReduced_of_etale_of_domain
      (R := MvPolynomial (Fin n) K) (S := Localization.Away r)
  constructor
  intro x hx
  apply eq_zero_of_localization
  intro m hm
  have hmprime : m.IsPrime := hm.isPrime
  obtain ⟨r, hrs, hrm⟩ : ∃ r ∈ s, r ∉ m := by
    by_contra h
    push Not at h
    have hle : Ideal.span s ≤ m := Ideal.span_le.mpr h
    rw [hs] at hle
    exact hm.ne_top (top_unique hle)
  letI : IsReduced (Localization.Away r) := hredAway r hrs
  have hxaway : algebraMap A (Localization.Away r) x = 0 :=
    (hx.map (algebraMap A (Localization.Away r))).eq_zero
  obtain ⟨y, hy⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers r)
      (Localization.Away r) x).mp hxaway
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (y : A) r).mp y.prop
  apply (IsLocalization.map_units (M := m.primeCompl) (Localization.AtPrime m)
    (⟨(y : A), fun hym ↦ hrm (hmprime.mem_of_pow_mem n (hn ▸ hym))⟩ :
      m.primeCompl)).mul_right_inj.mp
  rw [← map_mul, hy, map_zero, mul_zero]

end Theory.AlgebraicGroup.Bor1

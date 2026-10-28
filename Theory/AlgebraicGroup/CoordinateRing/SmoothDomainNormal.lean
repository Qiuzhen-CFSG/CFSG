module

public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Integral closedness of smooth domains

An étale domain over an integrally closed domain is integrally closed. To prove this,
localize the base at its nonzero elements. The resulting generic fiber is an unramified
finite-dimensional domain over a field, hence a field of fractions of the original
algebra. Smooth base change for integral closure then says that its integral elements
already belong to the original algebra.

A smooth domain over a field is locally standard étale over a polynomial ring. Applying
the preceding result on those principal open charts and the maximal-localization
criterion proves integral closedness in every dimension.

This supplies the affine input to Borel, *Linear Algebraic Groups*, AG.18.1
(`refs/KGroup/Bor1/ChapterAG.tex`), used for smooth orbit normality in §10.4.
The integral-closure base-change theorem and étale presentations are supplied by
Mathlib's `Smooth.IntegralClosure` and `Unramified.LocalStructure`.
-/

namespace Theory.AlgebraicGroup

open scoped TensorProduct nonZeroDivisors

/-- An étale algebra which is a domain over an integrally closed domain is
integrally closed. -/
public theorem isIntegrallyClosed_of_etale_of_isDomain (R S : Type*)
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra.Etale R S] [IsIntegrallyClosed R] :
    IsIntegrallyClosed S := by
  let K := FractionRing R
  let T := S ⊗[R] K
  let M := Algebra.algebraMapSubmonoid S R⁰
  have hinj : Function.Injective (algebraMap R S) :=
    FaithfulSMul.algebraMap_injective R S
  have hM : M ≤ S⁰ := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      (fun h ↦ (mem_nonZeroDivisors_iff_ne_zero.mp hx) (hinj (h.trans (map_zero _).symm)))
  let _ : IsLocalization M T := inferInstance
  let _ : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T hM
  let _ : Algebra K T := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra.Etale K T :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.commRight R K S)
  let _ : Module.Finite K T := Algebra.FormallyUnramified.finite_of_free K T
  have hfield : IsField T := isField_of_isIntegral_of_isField' (R := K) (S := T)
    (Field.toIsField K)
  let _ : Field T := hfield.toField
  let _ : IsFractionRing S T := IsLocalization.of_le M S⁰ hM (by
    intro r hr
    apply isUnit_iff_ne_zero.mpr
    exact fun h ↦ (mem_nonZeroDivisors_iff_ne_zero.mp hr)
      (IsLocalization.injective T hM (h.trans (map_zero _).symm)))
  apply (isIntegrallyClosed_iff T).mpr
  intro x hx
  obtain ⟨y, hy⟩ :=
    (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S) (B := K)).surjective
      ⟨x, hx⟩
  have h : ∀ y : S ⊗[R] integralClosure R K,
      ((TensorProduct.toIntegralClosure R S K y : integralClosure S T) : T) ∈
        (algebraMap S T).range := by
    intro y
    induction y with
    | zero => exact ⟨0, by simp⟩
    | add a b ha hb => simpa only [map_add, Subalgebra.coe_add] using
        (algebraMap S T).range.add_mem ha hb
    | tmul a b =>
      obtain ⟨r, hr⟩ := (isIntegrallyClosed_iff K).mp ‹IsIntegrallyClosed R› b.2
      refine ⟨a * algebraMap R S r, ?_⟩
      change (a * algebraMap R S r) ⊗ₜ[R] (1 : K) = a ⊗ₜ[R] (b : K)
      rw [← hr, Algebra.algebraMap_eq_smul_one (R := R) (A := K),
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]
  change x ∈ (algebraMap S T).range
  simpa only [hy] using h y

/-- A smooth domain over a field is integrally closed, with no dimension restriction. -/
public theorem isIntegrallyClosed_of_smooth_of_isDomain (k A : Type*)
    [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.Smooth k A] :
    IsIntegrallyClosed A := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  let _ : p.IsPrime := hp.isPrime
  obtain ⟨f, hfp, n, algPB, hTower, hStandardEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (S := A) (p := p)
  let P := MvPolynomial (Fin n) k
  let B := Localization.Away f
  let _ : Algebra P B := algPB
  let _ : IsScalarTower k P B := hTower
  let _ : Algebra.IsStandardEtale P B := hStandardEtale
  let _ : IsDomain B := Localization.Away.isDomain (fun h ↦ hfp (h ▸ p.zero_mem))
  let _ : IsIntegrallyClosed P := inferInstance
  let _ : IsIntegrallyClosed B := isIntegrallyClosed_of_etale_of_isDomain P B
  let q : Ideal B := p.map (algebraMap A B)
  have hdisj : Disjoint ((Submonoid.powers f : Set A)) (p : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hfp
  let _ : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) B p inferInstance hdisj
  let _ : q.LiesOver p :=
    IsLocalization.liesOver_map_of_isPrime_disjoint (.powers f) B hdisj
  let _ : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q)
      q.primeCompl q.primeCompl_le_nonZeroDivisors
  let _ : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    have hloc :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (M := Submonoid.powers f) (Localization.AtPrime q) q
    have hqp : q.comap (algebraMap A B) = p :=
      (Ideal.LiesOver.over (p := p) (P := q)).symm
    simpa only [hqp] using hloc
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime q)
      (Localization.AtPrime p)).toRingEquiv

end Theory.AlgebraicGroup

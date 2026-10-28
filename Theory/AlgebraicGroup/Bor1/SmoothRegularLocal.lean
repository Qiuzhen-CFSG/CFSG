module

public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Theory.AlgebraicGroup.Bor1.FormallyUnramifiedFlatRegularLocal

namespace Theory.AlgebraicGroup.Bor1

universe u v

variable (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]

/-- Every local ring of a smooth algebra over a field is regular. -/
public theorem isRegularLocalRing_localizationAtPrime_of_smooth
    [Algebra.Smooth k A] (p : Ideal A) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  have _ : Algebra.IsSmoothAt k p := inferInstance
  obtain ⟨f, hfp, n, algPB, hTower, hStandardEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial
      (R := k) (S := A) (p := p)
  let P := MvPolynomial (Fin n) k
  let B := Localization.Away f
  let _ : Algebra P B := algPB
  let _ : IsScalarTower k P B := hTower
  let _ : Algebra.IsStandardEtale P B := hStandardEtale
  let q : Ideal B := p.map (algebraMap A B)
  have hdisj : Disjoint ((Submonoid.powers f : Set A)) (p : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hfp
  let _ : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) B p inferInstance hdisj
  let _ : q.LiesOver p :=
    IsLocalization.liesOver_map_of_isPrime_disjoint (.powers f) B hdisj
  let r : Ideal P := q.under P
  let _ : r.IsPrime := Ideal.IsPrime.under P q
  let _ : q.LiesOver r := ⟨rfl⟩
  let _ : Algebra (Localization.AtPrime r) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver r q
  let _ : Localization.AtPrime.IsLiesOverAlgebra r q := inferInstance
  let _ : IsRegularRing P := by
    dsimp [P]
    infer_instance
  let _ : IsRegularLocalRing (Localization.AtPrime r) := inferInstance
  let _ : Algebra.Etale P B := inferInstance
  let _ : Algebra.IsUnramifiedAt P q := inferInstance
  let _ : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing P B
  let _ : IsNoetherianRing (Localization.AtPrime q) := inferInstance
  let _ : Algebra.EssFiniteType (Localization.AtPrime r) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp P _ _
  let _ : IsLocalHom
      (algebraMap (Localization.AtPrime r) (Localization.AtPrime q)) := by
    rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
    exact Localization.isLocalHom_localRingHom r q (algebraMap P B)
      Ideal.LiesOver.over
  have hregq : IsRegularLocalRing (Localization.AtPrime q) :=
    isRegularLocalRing_of_formallyUnramified_of_flat
      (R := Localization.AtPrime r) (S := Localization.AtPrime q)
  let _ : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    have hloc :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (M := Submonoid.powers f) (Localization.AtPrime q) q
    have hqp : q.comap (algebraMap A B) = p :=
      (Ideal.LiesOver.over (p := p) (P := q)).symm
    simpa only [hqp] using hloc
  let e : Localization.AtPrime q ≃ₐ[A] Localization.AtPrime p :=
    IsLocalization.algEquiv p.primeCompl _ _
  let _ : IsRegularLocalRing (Localization.AtPrime q) := hregq
  exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv

end Theory.AlgebraicGroup.Bor1

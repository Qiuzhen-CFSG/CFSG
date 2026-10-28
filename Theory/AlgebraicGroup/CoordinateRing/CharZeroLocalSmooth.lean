module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Theory.AlgebraicGroup.Bor1.FormallyUnramifiedFlatRegularLocal
public import Theory.AlgebraicGroup.CoordinateRing.LocalSmoothRegular

/-!
# Cotangent injectivity over a characteristic-zero field

This module establishes the characteristic-zero local smoothness criterion for
finite-type algebras.  For a Noetherian local algebra whose residue field is
essentially of finite type, the map from the cotangent space to Kahler
differentials after residue base change is injective.

The proof follows [Stacks Project, Lemma 10.140.4 (tag 00TU)]: characteristic
zero makes the base field perfect, so the essentially finite-type residue
field is formally smooth.  Its map from the square-zero quotient by the square
of the maximal ideal therefore has an algebra section.  The section/retraction
equivalence for the cotangent map then supplies a left inverse.  This is the
cotangent-exactness input for the local smooth/regular criterion of tag 00TV.
For a prime localization that is regular local, characteristic zero also gives
a finite separating transcendence basis of its residue field.  The exact
cotangent sequence, the resulting differential-dimension equality, and the
presentation Jacobian criterion from tag 00TT then prove smoothness at the
prime through `LocalSmoothRegular`.

For later assembly of that criterion, the module also records the already
available converse direction: a finite-type algebra smooth at a prime has a
regular local ring there.  This uses the standard-etale local structure of a
smooth morphism and regularity transfer along a flat formally unramified local
map.
-/

namespace Theory.AlgebraicGroup

open IsLocalRing

universe u v

/-- Over a characteristic-zero field, the residue cotangent map of an
essentially finite-type Noetherian local algebra is injective. -/
public theorem charZero_local_cotangentToKaehler_injective
    (k : Type u) (R : Type v) [Field k] [CharZero k]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra k R]
    [Algebra.EssFiniteType k (ResidueField R)] :
    Function.Injective
      (KaehlerDifferential.kerCotangentToTensor k R (ResidueField R)) := by
  let K := ResidueField R
  let f : R →ₐ[k] K := IsScalarTower.toAlgHom k R K
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  let _ : Algebra.FormallySmooth k K := inferInstance
  have hsquareLift : Function.Surjective f.kerSquareLift :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hf
  have hker : RingHom.ker f.kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  let g := Algebra.FormallySmooth.liftOfSurjective
    (AlgHom.id k K) f.kerSquareLift hsquareLift ⟨2, hker⟩
  have hg : f.kerSquareLift.comp g = AlgHom.id k K :=
    Algebra.FormallySmooth.comp_liftOfSurjective
      (AlgHom.id k K) f.kerSquareLift hsquareLift ⟨2, hker⟩
  let l := (retractionKerCotangentToTensorEquivSection (R := k) hf).symm
    ⟨g, hg⟩
  exact Function.HasLeftInverse.injective ⟨l.1, LinearMap.congr_fun l.2⟩

/-- A finite-type algebra over a characteristic-zero field is smooth at every
prime whose localization is a regular local ring. -/
public theorem finiteType_charZero_isSmoothAt_of_regularLocal
    (k : Type u) (S : Type v) [Field k] [CharZero k]
    [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (q : Ideal S) [q.IsPrime]
    (hq : IsRegularLocalRing (Localization.AtPrime q)) :
    Algebra.IsSmoothAt k q := by
  let R := Localization.AtPrime q
  let K := ResidueField R
  let _ : Algebra.EssFiniteType k R := inferInstance
  let _ : Algebra.EssFiniteType k K := Algebra.EssFiniteType.comp k R K
  apply
    finiteType_isSmoothAt_of_regularLocal_of_cotangentToKaehler_injective_of_separablyGenerated
      k S q hq
  · exact charZero_local_cotangentToKaehler_injective k R
  · exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K

private theorem finiteType_isRegularLocalRing_of_isSmoothAt
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime]
    (hq : Algebra.IsSmoothAt k q) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let _ : Algebra.FinitePresentation k S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let _ : Algebra.IsSmoothAt k q := hq
  obtain ⟨f, hfq, n, algPB, hTower, hStandardEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial
      (R := k) (S := S) (p := q)
  let P := MvPolynomial (Fin n) k
  let B := Localization.Away f
  let _ : Algebra P B := algPB
  let _ : IsScalarTower k P B := hTower
  let _ : Algebra.IsStandardEtale P B := hStandardEtale
  let Q : Ideal B := q.map (algebraMap S B)
  have hdisj : Disjoint ((Submonoid.powers f : Set S)) (q : Set S) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hfq
  let _ : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) B q inferInstance hdisj
  let _ : Q.LiesOver q :=
    IsLocalization.liesOver_map_of_isPrime_disjoint (.powers f) B hdisj
  let r : Ideal P := Q.under P
  let _ : r.IsPrime := Ideal.IsPrime.under P Q
  let _ : Q.LiesOver r := ⟨rfl⟩
  let _ : Algebra (Localization.AtPrime r) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver r Q
  let _ : Localization.AtPrime.IsLiesOverAlgebra r Q := inferInstance
  let _ : IsRegularRing P := by
    dsimp [P]
    infer_instance
  let _ : IsRegularLocalRing (Localization.AtPrime r) := inferInstance
  let _ : Algebra.Etale P B := inferInstance
  let _ : Algebra.IsUnramifiedAt P Q := inferInstance
  let _ : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing P B
  let _ : IsNoetherianRing (Localization.AtPrime Q) := inferInstance
  let _ : Algebra.EssFiniteType (Localization.AtPrime r) (Localization.AtPrime Q) :=
    Algebra.EssFiniteType.of_comp P _ _
  let _ : IsLocalHom
      (algebraMap (Localization.AtPrime r) (Localization.AtPrime Q)) := by
    rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
    exact Localization.isLocalHom_localRingHom r Q (algebraMap P B)
      Ideal.LiesOver.over
  have hregQ : IsRegularLocalRing (Localization.AtPrime Q) :=
    Bor1.isRegularLocalRing_of_formallyUnramified_of_flat
      (R := Localization.AtPrime r) (S := Localization.AtPrime Q)
  let _ : IsLocalization.AtPrime (Localization.AtPrime Q) q := by
    have hloc :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (M := Submonoid.powers f) (Localization.AtPrime Q) Q
    have hQq : Q.comap (algebraMap S B) = q :=
      (Ideal.LiesOver.over (p := q) (P := Q)).symm
    simpa only [hQq] using hloc
  let e : Localization.AtPrime Q ≃ₐ[S] Localization.AtPrime q :=
    IsLocalization.algEquiv q.primeCompl _ _
  let _ : IsRegularLocalRing (Localization.AtPrime Q) := hregQ
  exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv

/-- Over a characteristic-zero field, a finite-type algebra is smooth at a
prime exactly when its local ring at that prime is regular. -/
public theorem finiteType_charZero_isSmoothAt_iff_regularLocal
    (k : Type u) (S : Type v) [Field k] [CharZero k]
    [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (q : Ideal S) [q.IsPrime] :
    Algebra.IsSmoothAt k q ↔ IsRegularLocalRing (Localization.AtPrime q) := by
  constructor
  · exact finiteType_isRegularLocalRing_of_isSmoothAt k S q
  · exact finiteType_charZero_isSmoothAt_of_regularLocal k S q

end Theory.AlgebraicGroup

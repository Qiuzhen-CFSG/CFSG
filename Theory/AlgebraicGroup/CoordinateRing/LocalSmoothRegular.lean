module

public import Theory.AlgebraicGroup.CoordinateRing.LocalSmoothDimension

/-!
# Regular local rings and smoothness at a prime

Let `q` be a prime of a finite-type algebra `S` over a field `k`, let
`R = S_q`, and let `K` be the residue field of `R`.  This module proves the
regular-local smoothness bridge used by the coordinate-ring development.  Its
residue-field hypothesis is a finite separating transcendence basis: this is
the separably-generated condition in Stacks Project, Tag 00TV.

The proof uses the exact cotangent sequence
`m/m^2 -> K ⊗_R Ω[R/k] -> Ω[K/k] -> 0`.  Injectivity of its first map
makes dimensions additive.  Regularity identifies the dimension of `m/m^2`
with `height(q)`, while a separating transcendence basis identifies the
dimension of `Ω[K/k]` with `trdeg_k K`.  The resulting equality satisfies the
local Kähler-dimension criterion in `LocalSmoothDimension`, the implication
(2) to (1) of Stacks Project, Tag 00TT.

The separably-generated hypothesis is essential: regularity and cotangent-map
injectivity alone do not imply smoothness for an inseparable field extension.
-/

open IsLocalRing Module
open scoped IntermediateField.algebraAdjoinAdjoin TensorProduct

universe u v

namespace Theory.AlgebraicGroup

set_option linter.style.haveILetI false

private lemma finrank_kaehlerDifferential_eq_card_of_separablyGenerated
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (s : Finset K) (hs : IsTranscendenceBasis k ((↑) : s → K))
    (hseparable : Algebra.IsSeparable
      (IntermediateField.adjoin k (s : Set K)) K) :
    Module.finrank K Ω[K⁄k] = s.card := by
  let x : s → K := (↑)
  let A := Algebra.adjoin k (Set.range x)
  let F := IntermediateField.adjoin k (Set.range x)
  letI : Algebra.IsSeparable
      (IntermediateField.adjoin k (Set.range x)) K := by
    convert! hseparable <;> simp [x]
  let e : MvPolynomial s k ≃ₐ[k] A := hs.1.aevalEquiv
  letI : Algebra (MvPolynomial s k) A := e.toAlgHom.toAlgebra
  letI : IsScalarTower k (MvPolynomial s k) A :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (e.commutes r).symm
  let e' : MvPolynomial s k ≃ₐ[MvPolynomial s k] A :=
    AlgEquiv.ofBijective (Algebra.ofId (MvPolynomial s k) A) e.bijective
  letI : Algebra.FormallyEtale (MvPolynomial s k) A :=
    Algebra.FormallyEtale.of_equiv e'
  let bA : Basis s A Ω[A⁄k] :=
    ((KaehlerDifferential.mvPolynomialBasis k s).baseChange A).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
        k (MvPolynomial s k) A)
  letI : Algebra.FormallyEtale A F :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  let bF : Basis s F Ω[F⁄k] :=
    (bA.baseChange F).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A F)
  letI : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  let bK : Basis s K Ω[K⁄k] :=
    (bF.baseChange K).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k F K)
  exact Module.finrank_eq_card_finset_basis bK

private lemma finrank_tensorKaehler_eq_cotangent_add_residue
    (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
    [IsLocalRing R] [IsNoetherianRing R] [Algebra.EssFiniteType k R]
    (hinjective : Function.Injective
      (KaehlerDifferential.kerCotangentToTensor k R (ResidueField R))) :
    Module.finrank (ResidueField R) ((ResidueField R) ⊗[R] Ω[R⁄k]) =
      Module.finrank (ResidueField R) (CotangentSpace R) +
        Module.finrank (ResidueField R) Ω[ResidueField R⁄k] := by
  let K := ResidueField R
  let hres : Function.Surjective (algebraMap R K) := residue_surjective
  have hker : RingHom.ker (algebraMap R K) = maximalIdeal R := by
    rw [ResidueField.algebraMap_eq]
    exact ker_residue
  let e : CotangentSpace R ≃ₗ[R]
      (RingHom.ker (algebraMap R K)).Cotangent :=
    Ideal.Cotangent.equivOfEq _ _ hker.symm
  let f : CotangentSpace R →ₗ[K] K ⊗[R] Ω[R⁄k] :=
    ((KaehlerDifferential.kerCotangentToTensor k R K).comp e.toLinearMap)
      |>.extendScalarsOfSurjective hres
  let g : K ⊗[R] Ω[R⁄k] →ₗ[K] Ω[K⁄k] :=
    KaehlerDifferential.mapBaseChange k R K
  letI : Algebra.EssFiniteType k K := Algebra.EssFiniteType.comp k R K
  have hexact : Function.Exact f g := by
    have h :=
      KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k R K hres
    intro y
    constructor
    · intro hy
      obtain ⟨z, hz⟩ := (h y).mp hy
      refine ⟨e.symm z, ?_⟩
      simpa [f] using hz
    · rintro ⟨x, rfl⟩
      apply (h _).mpr
      refine ⟨e x, ?_⟩
      simp [f]
  have hsurjective : Function.Surjective g :=
    KaehlerDifferential.mapBaseChange_surjective k R K hres
  have hinjective' : Function.Injective f := hinjective.comp e.injective
  have hrange : LinearMap.ker g = LinearMap.range f :=
    LinearMap.exact_iff.mp hexact
  rw [← LinearMap.finrank_range_add_finrank_ker g, hrange]
  rw [LinearMap.finrank_range_of_inj hinjective']
  rw [LinearMap.range_eq_top.mpr hsurjective, finrank_top]
  simp [K, Nat.add_comm]

public theorem
    finiteType_isSmoothAt_of_regularLocal_of_cotangentToKaehler_injective_of_separablyGenerated
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime]
    (hregular : IsRegularLocalRing (Localization.AtPrime q))
    (hinjective : Function.Injective
      (KaehlerDifferential.kerCotangentToTensor k
        (Localization.AtPrime q)
        (ResidueField (Localization.AtPrime q))))
    (hseparable :
      ∃ s : Finset (ResidueField (Localization.AtPrime q)),
        IsTranscendenceBasis k
          ((↑) : s → ResidueField (Localization.AtPrime q)) ∧
        Algebra.IsSeparable
          (IntermediateField.adjoin k
            (s : Set (ResidueField (Localization.AtPrime q))))
          (ResidueField (Localization.AtPrime q))) :
    Algebra.IsSmoothAt k q := by
  let R := Localization.AtPrime q
  let K := ResidueField R
  letI : IsRegularLocalRing R := hregular
  letI : Algebra.EssFiniteType k R := inferInstance
  obtain ⟨s, hs, hsep⟩ := hseparable
  have hexact :
      Module.finrank K (K ⊗[R] Ω[R⁄k]) =
        Module.finrank K (CotangentSpace R) + Module.finrank K Ω[K⁄k] :=
    finrank_tensorKaehler_eq_cotangent_add_residue k R hinjective
  have hregular' :
      (Module.finrank K (CotangentSpace R) : WithBot ℕ∞) = q.height := by
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp hregular
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q R] at h
    exact h
  have hfield : Module.finrank K Ω[K⁄k] = s.card :=
    finrank_kaehlerDifferential_eq_card_of_separablyGenerated k K s hs hsep
  have hcard : s.card = Cardinal.toNat (Algebra.trdeg k K) := by
    rw [← hs.cardinalMk_eq_trdeg]
    simp
  apply finiteType_isSmoothAt_of_finrank_tensorKaehler_le_height_add_trdeg k S q
  rw [hexact, Nat.cast_add, hregular', hfield, hcard]

end Theory.AlgebraicGroup

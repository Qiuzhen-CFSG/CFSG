module

public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.FiniteType

/-!
# A flat localization of a finite-type domain algebra

For an injective finite-type extension of domains `R → A`, with `R`
Noetherian, some nonzero source element `a` makes `A[1/a]` flat over `R`.
Choose a finite transcendence basis in a set of algebra generators. Its
adjoin is a polynomial algebra over `R`, and `A` is algebraic over that
adjoin. Clear denominators in the remaining generators, then spread a
fraction-field basis of the resulting finite module. The polynomial algebra
and its localizations are flat over `R`, so flatness composes.

Only a source-open patch is asserted. This avoids the stronger generic
freeness theorem for an algebra viewed as an infinite module over `R`.
The finite-module spreading argument is adapted from the checked private
lemmas in `Theory.AlgebraicGroup.Morphism.BijectiveCoordinatePowers.FlatOpen`.
It is used for the possibly inseparable homogeneous orbit map in Borel,
*Linear Algebraic Groups*, §11.15 (`refs/KGroup/Bor1/Chapter4.tex`).
-/

open scoped nonZeroDivisors
set_option linter.style.haveILetI false
universe u

namespace Theory.AlgebraicGroup.GenericFlat

private theorem exists_flat_away_of_finite
    {R B : Type*} [CommRing R] [CommRing B] [IsDomain R] [IsNoetherianRing R]
    [Algebra R B] [Module.Finite R B] :
    ∃ r : R, r ≠ 0 ∧ (Localization.awayMap (algebraMap R B) r).Flat := by
  let K := FractionRing R
  letI : Module.FinitePresentation R B := Module.finitePresentation_of_finite R B
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    R⁰ (LocalizedModule.mkLinearMap R⁰ B) K
  refine ⟨r, nonZeroDivisors.ne_zero hr, ?_⟩
  let Br := Localization.Away (algebraMap R B r)
  letI : Algebra (Localization.Away r) Br := localizationAlgebra (.powers r) B
  letI : IsScalarTower R (Localization.Away r) Br :=
    isScalarTower_localizationAlgebra (.powers r) B
  letI := hfree
  let e : LocalizedModule.Away r B ≃ₗ[Localization.Away r] Br :=
    (IsLocalizedModule.iso (.powers r)
      (IsScalarTower.toAlgHom R B Br).toLinearMap).extendScalarsOfIsLocalization
        (.powers r) (Localization.Away r)
  have hflat : Module.Flat (Localization.Away r) Br := Module.Flat.of_linearEquiv e.symm
  exact hflat

private theorem flat_away_mul
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (r c : R) (hf : (Localization.awayMap f r).Flat) :
    (Localization.awayMap f (r * c)).Flat := by
  let Rr := Localization.Away r
  let Ar := Localization.Away (f r)
  let Rrc := Localization.Away (algebraMap R Rr c)
  let Arc := Localization.Away (algebraMap A Ar (f c))
  letI : Algebra R A := f.toAlgebra
  let fr : Rr →+* Ar := Localization.awayMap f r
  have heq : fr (algebraMap R Rr c) = algebraMap A Ar (f c) := by
    exact IsLocalization.map_eq _ c
  letI : IsLocalization.Away (fr (algebraMap R Rr c)) Arc := heq.symm ▸ inferInstance
  let g : Rrc →+* Arc := IsLocalization.Away.map Rrc Arc fr (algebraMap R Rr c)
  have hflat : g.Flat := RingHom.Flat.propertyIsLocal.localizationAwayPreserves
    fr (algebraMap R Rr c) Rrc Arc hf
  letI : IsLocalization.Away (r * c) Rrc := inferInstance
  letI : IsLocalization.Away (f (r * c)) Arc := by
    rw [map_mul]
    infer_instance
  let eR : Localization.Away (r * c) ≃ₐ[R] Rrc :=
    IsLocalization.algEquiv (.powers (r * c)) _ _
  let eA : Arc ≃ₐ[A] Localization.Away (f (r * c)) :=
    IsLocalization.algEquiv (.powers (f (r * c))) _ _
  have he : Localization.awayMap f (r * c) =
      eA.toRingHom.comp (g.comp eR.toRingHom) := by
    apply IsLocalization.ringHom_ext (.powers (r * c))
    ext x
    change Localization.awayMap f (r * c) (algebraMap R _ x) =
      eA (g (eR (algebraMap R _ x)))
    rw [eR.commutes, IsScalarTower.algebraMap_apply R Rr Rrc]
    rw [show g (algebraMap Rr Rrc (algebraMap R Rr x)) =
        algebraMap Ar Arc (fr (algebraMap R Rr x)) from IsLocalization.map_eq _ _]
    rw [show fr (algebraMap R Rr x) = algebraMap A Ar (f x) from
      IsLocalization.map_eq _ _]
    rw [← IsScalarTower.algebraMap_apply A Ar Arc, eA.commutes]
    exact IsLocalization.map_eq _ _
  rw [he]
  exact (RingHom.Flat.of_bijective eR.bijective).comp hflat |>.comp
    (RingHom.Flat.of_bijective eA.bijective)

private theorem exists_finite_subalgebra_away
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R]
    [Algebra R A] [Algebra.FiniteType R A] [Algebra.IsAlgebraic R A] :
    ∃ (B : Subalgebra R A) (c : R), c ≠ 0 ∧ B.toSubmodule.FG ∧
      Function.Bijective (Localization.awayMap B.val.toRingHom (algebraMap R B c)) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  obtain ⟨c, hc, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples R s
  let B := Algebra.adjoin R ((fun x : A => c • x) '' (s : Set A))
  have hfg : B.toSubmodule.FG := fg_adjoin_of_finite
    (s.finite_toSet.image _) (by rintro _ ⟨x, hx, rfl⟩; exact hint x hx)
  refine ⟨B, c, hc, hfg, IsLocalization.map_injective_of_injective _ _ _ Subtype.val_injective, ?_⟩
  let d := algebraMap R A c
  let D : Subalgebra R A :=
    { carrier := {x | ∃ n : ℕ, d ^ n * x ∈ B}
      algebraMap_mem' := fun x => ⟨0, by simp⟩
      zero_mem' := ⟨0, by simp⟩
      one_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro x y ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have he : d ^ (m + n) * (x + y) =
            algebraMap R A (c ^ n) * (d ^ m * x) +
              algebraMap R A (c ^ m) * (d ^ n * y) := by
          simp only [map_pow, pow_add, d]
          ring
        rw [he]
        exact B.add_mem (B.mul_mem (B.algebraMap_mem _) hm)
          (B.mul_mem (B.algebraMap_mem _) hn)
      mul_mem' := by
        rintro x y ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have he : d ^ (m + n) * (x * y) = (d ^ m * x) * (d ^ n * y) := by
          rw [pow_add]
          ring
        rw [he]
        exact B.mul_mem hm hn }
  have hD : D = ⊤ := by
    apply top_unique
    rw [← hs]
    apply Algebra.adjoin_le
    intro x hx
    refine ⟨1, ?_⟩
    rw [pow_one]
    change algebraMap R A c * x ∈ B
    rw [← Algebra.smul_def]
    exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
  apply Localization.awayMap_surjective_iff.mpr
  intro x
  have hx : x ∈ D := by rw [hD]; trivial
  obtain ⟨n, hn⟩ := hx
  exact ⟨⟨d ^ n * x, hn⟩, n, rfl⟩

private theorem exists_flat_away_of_isAlgebraic
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] [IsNoetherianRing R]
    [Algebra R A] [Algebra.FiniteType R A] [Algebra.IsAlgebraic R A] :
    ∃ c : R, c ≠ 0 ∧ (Localization.awayMap (algebraMap R A) c).Flat := by
  obtain ⟨B, c, hc, hfg, hbij⟩ := exists_finite_subalgebra_away (R := R) (A := A)
  letI : Module.Finite R B := ⟨(Submodule.fg_top _).mpr hfg⟩
  obtain ⟨r, hr, hflat⟩ := exists_flat_away_of_finite (R := R) (B := B)
  refine ⟨r * c, mul_ne_zero hr hc, ?_⟩
  have hflat' := flat_away_mul (algebraMap R B) r c hflat
  have hbij' := Localization.awayMap_bijective_of_dvd B.val.toRingHom
    (map_dvd (algebraMap R B) (dvd_mul_left c r)) hbij
  have he : Localization.awayMap (algebraMap R A) (r * c) =
      (Localization.awayMap B.val.toRingHom (algebraMap R B (r * c))).comp
        (Localization.awayMap (algebraMap R B) (r * c)) := by
    apply IsLocalization.ringHom_ext (.powers (r * c))
    ext x
    change Localization.awayMap (algebraMap R A) (r * c) (algebraMap R _ x) =
      Localization.awayMap B.val.toRingHom (algebraMap R B (r * c))
        (Localization.awayMap (algebraMap R B) (r * c) (algebraMap R _ x))
    simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  rw [he]
  exact hflat'.comp (RingHom.Flat.of_bijective hbij')

/-- An injective finite-type extension of domains over a Noetherian base
becomes flat over the base after inverting one nonzero element of the source. -/
public theorem exists_flat_source_localization
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] [IsDomain A]
    [IsNoetherianRing R] [Algebra R A] [FaithfulSMul R A]
    [Algebra.FiniteType R A] :
    ∃ a : A, a ≠ 0 ∧ (algebraMap R (Localization.Away a)).Flat := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  letI : Algebra.IsAlgebraic (Algebra.adjoin R (s : Set A)) A := by
    rw [hs]
    letI : Algebra.IsIntegral (⊤ : Subalgebra R A) A :=
      Algebra.isIntegral_of_surjective (fun a => ⟨⟨a, by trivial⟩, rfl⟩)
    infer_instance
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := R) (s : Set A)
  letI : Finite t := (s.finite_toSet.subset hts).to_subtype
  let C := Algebra.adjoin R (Set.range ((↑) : t → A))
  let e : MvPolynomial t R ≃ₐ[R] C := ht.1.aevalEquiv
  letI : IsNoetherianRing C :=
    isNoetherianRing_of_surjective (MvPolynomial t R) C e.toRingHom e.surjective
  letI : Algebra.IsAlgebraic C A := ht.isAlgebraic
  letI : Algebra.FiniteType C A := Algebra.FiniteType.of_restrictScalars_finiteType R C A
  obtain ⟨c, hc, hflat⟩ := exists_flat_away_of_isAlgebraic (R := C) (A := A)
  refine ⟨(c : A), fun h => hc (Subtype.ext h), ?_⟩
  have hRC : (algebraMap R C).Flat := by
    rw [RingHom.flat_algebraMap_iff]
    exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  have hloc : (algebraMap C (Localization.Away c)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (.powers c))
  have hcomp := (hRC.comp hloc).comp hflat
  have he : algebraMap R (Localization.Away (c : A)) =
      (Localization.awayMap (algebraMap C A) c).comp
        ((algebraMap C (Localization.Away c)).comp (algebraMap R C)) := by
    ext r
    change algebraMap A (Localization.Away (c : A)) (algebraMap R A r) =
      Localization.awayMap (algebraMap C A) c
        (algebraMap C (Localization.Away c) (algebraMap R C r))
    rw [show Localization.awayMap (algebraMap C A) c
        (algebraMap C (Localization.Away c) (algebraMap R C r)) =
      algebraMap A (Localization.Away (c : A))
        (algebraMap C A (algebraMap R C r)) from IsLocalization.map_eq _ _]
    rfl
  rw [he]
  exact hcomp

end Theory.AlgebraicGroup.GenericFlat

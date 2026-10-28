module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.RingHom.FiniteType
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.ConilpotentCurve

/-!
# Finiteness of primitive Hopf-curve maps

This module proves that a transcendental primitive element of a finite-type
domain of transcendence degree one induces a finite map from the polynomial
ring. In geometric terms, the corresponding dominant homomorphism of affine
group curves to the additive group is finite.

The proof is the coordinate-ring translation argument underlying the
finite-kernel step in the development of GLS Proposition 1.3.5(c). First,
transcendence degree one makes the coordinate ring algebraic over `k[t]`, so
finite type supplies a common denominator after whose localization it is
finite. Every `k`-point of the Hopf algebra gives a left translation, and
primitivity of `t` identifies the translated denominator with its polynomial
Taylor translate. The finite-type Nullstellensatz separates nonzero elements
by `k`-points; transcendence of `t` therefore makes its point-values infinite.
Consequently the Taylor translates of the denominator span the unit ideal,
and finite generation descends from these localizations.

No affine-line classification, one-parameter subgroup theorem, primitive
generator theorem, or polynomialization result is used.
-/

open scoped TensorProduct

universe u v

namespace Theory.AlgebraicGroup

set_option linter.style.haveILetI false

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

private lemma localized_mem_adjoin
    (s : Finset S) (hs : Algebra.adjoin R (s : Set S) = ⊤) (f : R) :
    ∀ z : Localization (Algebra.algebraMapSubmonoid S (.powers f)),
      z ∈ Algebra.adjoin (Localization.Away f)
        (algebraMap S (Localization (Algebra.algebraMapSubmonoid S (.powers f))) ''
          (s : Set S)) := by
  let Sₘ := Localization (Algebra.algebraMapSubmonoid S (.powers f))
  let Rₘ := Localization.Away f
  letI : Algebra Rₘ Sₘ := localizationAlgebra (.powers f) S
  let C := Algebra.adjoin Rₘ (algebraMap S Sₘ '' (s : Set S))
  have hmap : ∀ x : S, algebraMap S Sₘ x ∈ C := by
    intro x
    have hx : x ∈ Algebra.adjoin R (s : Set S) := by simp [hs]
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap r =>
        rw [← IsScalarTower.algebraMap_apply R S Sₘ,
          IsScalarTower.algebraMap_apply R Rₘ Sₘ]
        exact C.algebraMap_mem _
    | add x y _ _ hx hy => simpa only [map_add] using C.add_mem hx hy
    | mul x y _ _ hx hy => simpa only [map_mul] using C.mul_mem hx hy
  intro z
  refine Localization.induction_on z ?_
  rintro ⟨x, d⟩
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  apply C.mul_mem (hmap x)
  obtain ⟨r, hr, hd⟩ := d.2
  have hdsub : d =
      ⟨algebraMap R S r,
        Algebra.mem_algebraMapSubmonoid_of_mem (S := S) ⟨r, hr⟩⟩ :=
    Subtype.ext hd.symm
  have hfrac : IsLocalization.mk' Sₘ 1 d =
      algebraMap Rₘ Sₘ (IsLocalization.mk' Rₘ 1 ⟨r, hr⟩) := by
    calc
      IsLocalization.mk' Sₘ 1 d =
          IsLocalization.mk' Sₘ (algebraMap R S 1)
            ⟨algebraMap R S r,
              Algebra.mem_algebraMapSubmonoid_of_mem (S := S) ⟨r, hr⟩⟩ := by
                rw [map_one, hdsub]
      _ = algebraMap Rₘ Sₘ (IsLocalization.mk' Rₘ 1 ⟨r, hr⟩) :=
        (IsLocalization.algebraMap_mk' S Rₘ Sₘ 1 ⟨r, hr⟩).symm
  rw [hfrac]
  exact C.algebraMap_mem _

private lemma finite_localization_of_integral_multiples
    (s : Finset S) (hs : Algebra.adjoin R (s : Set S) = ⊤) (f : R)
    (hint : ∀ x ∈ s, IsIntegral R (f • x)) :
    Module.Finite (Localization.Away f)
      (Localization (Algebra.algebraMapSubmonoid S (.powers f))) := by
  let Sₘ := Localization (Algebra.algebraMapSubmonoid S (.powers f))
  let Rₘ := Localization.Away f
  letI : Algebra Rₘ Sₘ := localizationAlgebra (.powers f) S
  let C := Algebra.adjoin Rₘ (algebraMap S Sₘ '' (s : Set S))
  have hgen : C = ⊤ := by
    apply top_unique
    intro z _
    exact localized_mem_adjoin s hs f z
  have hint' : ∀ y ∈ (algebraMap S Sₘ '' (s : Set S)), IsIntegral Rₘ y := by
    rintro y ⟨x, hx, rfl⟩
    have hxint := hint x hx
    have hmapped : IsIntegral Rₘ (algebraMap S Sₘ (f • x)) :=
      IsIntegral.map_of_comp_eq (algebraMap R Rₘ) (algebraMap S Sₘ)
        (by
          ext r
          change algebraMap Rₘ Sₘ (algebraMap R Rₘ r) =
            algebraMap S Sₘ (algebraMap R S r)
          rw [← IsScalarTower.algebraMap_apply R Rₘ Sₘ,
            ← IsScalarTower.algebraMap_apply R S Sₘ])
        hxint
    let hfunit : IsUnit (algebraMap R Rₘ f) :=
      IsLocalization.Away.algebraMap_isUnit f
    let uf : Rₘˣ := hfunit.unit
    have huf : (↑uf : Rₘ) = algebraMap R Rₘ f := hfunit.unit_spec
    apply IsIntegral.of_mul_unit
        (r := (↑(uf⁻¹) : Rₘ)) (y := algebraMap Rₘ Sₘ (↑uf : Rₘ))
    · calc
        algebraMap Rₘ Sₘ (↑(uf⁻¹) : Rₘ) * algebraMap Rₘ Sₘ (↑uf : Rₘ) =
            algebraMap Rₘ Sₘ ((↑(uf⁻¹) : Rₘ) * (↑uf : Rₘ)) := by rw [map_mul]
        _ = 1 := by simp
    · convert hmapped using 1
      simp only [Algebra.smul_def, map_mul]
      rw [← IsScalarTower.algebraMap_apply R S Sₘ,
        IsScalarTower.algebraMap_apply R Rₘ Sₘ, ← huf]
      exact mul_comm _ _
  have hfinite : Module.Finite Rₘ C :=
    Algebra.finite_adjoin_of_finite_of_isIntegral
      ((Finset.finite_toSet s).image (algebraMap S Sₘ)) hint'
  rw [hgen] at hfinite
  letI := hfinite
  exact Module.Finite.equiv Subalgebra.topEquiv.toLinearEquiv

private lemma finite_localizedModule_of_integral_multiples
    (s : Finset S) (hs : Algebra.adjoin R (s : Set S) = ⊤) (f : R)
    (hint : ∀ x ∈ s, IsIntegral R (f • x)) :
    Module.Finite (Localization.Away f) (LocalizedModule.Away f S) := by
  let Sₘ := Localization (Algebra.algebraMapSubmonoid S (.powers f))
  let Rₘ := Localization.Away f
  letI : Algebra Rₘ Sₘ := localizationAlgebra (.powers f) S
  have hfinite : Module.Finite Rₘ Sₘ :=
    finite_localization_of_integral_multiples s hs f hint
  letI : Module.Finite Rₘ Sₘ := hfinite
  let numerator : S →ₗ[R] Sₘ := (IsScalarTower.toAlgHom R S Sₘ).toLinearMap
  let localized : S →ₗ[R] LocalizedModule.Away f S :=
    LocalizedModule.mkLinearMap (.powers f) S
  let e : Sₘ ≃ₗ[Rₘ] LocalizedModule.Away f S :=
    IsLocalizedModule.mapEquiv (.powers f) numerator localized Rₘ
      (LinearEquiv.refl R S)
  exact Module.Finite.equiv e

section Translation

variable {k : Type u} {A : Type v}
variable [Field k] [CommRing A] [HopfAlgebra k A]

private noncomputable def translation (p : WithConv (A →ₐ[k] k)) : A →ₐ[k] A :=
  (WithConv.toConv ((Algebra.ofId k A).comp p.ofConv) *
    WithConv.toConv (AlgHom.id k A)).ofConv

private lemma translation_mul (p q : WithConv (A →ₐ[k] k)) :
    (translation p).comp (translation q) = translation (q * p) := by
  have hscalar :
      (WithConv.toConv ((Algebra.ofId k A).comp p.ofConv) *
          WithConv.toConv (AlgHom.id k A)).ofConv.comp
          ((Algebra.ofId k A).comp q.ofConv) =
        (Algebra.ofId k A).comp q.ofConv := by
    ext x
    simp
  have hid :
      (WithConv.toConv ((Algebra.ofId k A).comp p.ofConv) *
          WithConv.toConv (AlgHom.id k A)).ofConv.comp (AlgHom.id k A) =
        (WithConv.toConv ((Algebra.ofId k A).comp p.ofConv) *
          WithConv.toConv (AlgHom.id k A)).ofConv := by rfl
  simp only [translation, AlgHom.comp_convMul_distrib, WithConv.toConv_ofConv]
  rw [hscalar, hid]
  simp only [WithConv.toConv_ofConv, mul_assoc]

private lemma translation_one :
    translation (1 : WithConv (A →ₐ[k] k)) = AlgHom.id k A := by
  have hscalar :
      WithConv.toConv ((Algebra.ofId k A).comp
          (1 : WithConv (A →ₐ[k] k)).ofConv) =
        (1 : WithConv (A →ₐ[k] A)) := by
    apply WithConv.ofConv_injective
    ext x
    simp
  rw [translation, hscalar, one_mul]

private noncomputable def translationEquiv (p : WithConv (A →ₐ[k] k)) : A ≃ₐ[k] A :=
  AlgEquiv.ofAlgHom (translation p) (translation p⁻¹)
    (by rw [translation_mul]; simp [translation_one])
    (by rw [translation_mul]; simp [translation_one])

private lemma translation_apply_of_primitive
    (p : WithConv (A →ₐ[k] k)) (t : A)
    (ht : Coalgebra.comul (R := k) t = t ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] t) :
    translation p t = algebraMap k A (p t) + t := by
  rw [translation, AlgHom.convMul_apply, ht]
  simp

private lemma translation_aeval_of_primitive
    (p : WithConv (A →ₐ[k] k)) (t : A)
    (ht : Coalgebra.comul (R := k) t = t ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] t)
    (q : Polynomial k) :
    translation p (Polynomial.aeval t q) =
      Polynomial.aeval t (Polynomial.taylor (p t) q) := by
  rw [← Polynomial.aeval_algHom_apply (translation p) t q,
    translation_apply_of_primitive p t ht]
  rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
  simp [add_comm]

private lemma adjoin_image_translation_eq_top
    (p : WithConv (A →ₐ[k] k)) (t : A)
    (ht : Coalgebra.comul (R := k) t = t ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] t)
    (s : Finset A)
    (hs : letI : Algebra (Polynomial k) A :=
        (Polynomial.aeval t).toRingHom.toAlgebra
      Algebra.adjoin (Polynomial k) (s : Set A) = ⊤) :
    letI : Algebra (Polynomial k) A := (Polynomial.aeval t).toRingHom.toAlgebra
    Algebra.adjoin (Polynomial k)
      ((fun z ↦ translationEquiv p z) '' (s : Set A)) = ⊤ := by
  letI : Algebra (Polynomial k) A := (Polynomial.aeval t).toRingHom.toAlgebra
  let C := Algebra.adjoin (Polynomial k)
    ((fun z ↦ translationEquiv p z) '' (s : Set A))
  apply top_unique
  intro x _
  have hx : (translationEquiv p).symm x ∈
      Algebra.adjoin (Polynomial k) (s : Set A) := by simp [hs]
  have hmap : ∀ y, y ∈ Algebra.adjoin (Polynomial k) (s : Set A) →
      translationEquiv p y ∈ C := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
        exact Algebra.subset_adjoin ⟨y, hy, rfl⟩
    | algebraMap q =>
        rw [show translationEquiv p (algebraMap (Polynomial k) A q) =
            algebraMap (Polynomial k) A (Polynomial.taylor (p t) q) by
          exact translation_aeval_of_primitive p t ht q]
        exact C.algebraMap_mem _
    | add x y _ _ hx hy => simpa only [map_add] using C.add_mem hx hy
    | mul x y _ _ hx hy => simpa only [map_mul] using C.mul_mem hx hy
  have htranslated : translationEquiv p ((translationEquiv p).symm x) ∈ C :=
    hmap _ hx
  simpa using htranslated

end Translation

section Transcendence

variable {k : Type u} {A : Type v}
variable [Field k] [CommRing A] [IsDomain A] [Algebra k A]

private lemma isAlgebraic_aeval_of_trdeg_eq_one
    (t : A) (ht : Transcendental k t) (htrdeg : Algebra.trdeg k A = 1) :
    letI : Algebra (Polynomial k) A := (Polynomial.aeval t).toRingHom.toAlgebra
    Algebra.IsAlgebraic (Polynomial k) A := by
  let x : ULift.{v} Unit → A := fun _ ↦ t
  have hx : AlgebraicIndependent k x := by
    rw [algebraicIndependent_unique_type_iff]
    exact ht
  have hle : Algebra.trdeg k A ≤ Cardinal.mk (ULift.{v} Unit) := by
    simp [htrdeg]
  have hbasis : IsTranscendenceBasis k x :=
    AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite hx hle
  have hrange : Set.range x = {t} := by
    ext a
    simp [x]
  haveI : Algebra.IsAlgebraic (Algebra.adjoin k {t}) A := by
    have halg := hbasis.isAlgebraic
    rw [hrange] at halg
    exact halg
  letI : Algebra (Polynomial k) A := (Polynomial.aeval t).toRingHom.toAlgebra
  let e := Polynomial.algEquivOfTranscendental k t ht
  apply Algebra.IsAlgebraic.of_ringHom_of_comp_eq e.toRingEquiv (RingHom.id A)
      e.surjective Function.injective_id
  apply Polynomial.ringHom_ext
  · intro c
    change ((e (Polynomial.C c) : Algebra.adjoin k {t}) : A) =
      Polynomial.aeval t (Polynomial.C c)
    simp [e]
  · change ((e Polynomial.X : Algebra.adjoin k {t}) : A) =
      Polynomial.aeval t Polynomial.X
    simp [e]

end Transcendence

section Characters

variable {k : Type u} {A : Type v}
variable [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
variable [Algebra.FiniteType k A]

private noncomputable def quotientCharacter (J : Ideal A) [J.IsMaximal] :
    (A ⧸ J) →ₐ[k] k := by
  letI : Field (A ⧸ J) := Ideal.Quotient.field J
  letI : Algebra.FiniteType k (A ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k J)
      (Ideal.Quotient.mkₐ_surjective k J)
  letI : Module.Finite k (A ⧸ J) :=
    finite_of_finite_type_of_isJacobsonRing k (A ⧸ J)
  exact IsAlgClosed.lift

private noncomputable def characterOfMaximal (J : Ideal A) [J.IsMaximal] : A →ₐ[k] k :=
  (quotientCharacter (k := k) J).comp (Ideal.Quotient.mkₐ k J)

private lemma characterOfMaximal_eq_zero_iff_mem
    (J : Ideal A) [J.IsMaximal] (a : A) :
    characterOfMaximal (k := k) J a = 0 ↔ a ∈ J := by
  letI : Field (A ⧸ J) := Ideal.Quotient.field J
  constructor
  · intro h
    have hq : Ideal.Quotient.mk J a = 0 :=
      (quotientCharacter (k := k) J).injective
        (by simpa [characterOfMaximal] using h)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  · intro h
    have hq : Ideal.Quotient.mk J a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr h
    change quotientCharacter (k := k) J (Ideal.Quotient.mk J a) = 0
    rw [hq, map_zero]

private lemma eq_zero_of_forall_character_eq_zero
    [IsReduced A] (a : A) (ha : ∀ φ : A →ₐ[k] k, φ a = 0) : a = 0 := by
  letI : IsJacobsonRing A :=
    isJacobsonRing_of_finiteType (A := k) (B := A)
  have hjac : a ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson]
    apply Ideal.mem_sInf.mpr
    intro J hJ
    letI : J.IsMaximal := hJ.2
    exact (characterOfMaximal_eq_zero_iff_mem (k := k) J a).mp
      (ha (characterOfMaximal (k := k) J))
  rw [← Ideal.radical_eq_jacobson, Ideal.radical_bot_of_isReduced] at hjac
  exact Ideal.mem_bot.mp hjac

private lemma character_values_infinite [IsDomain A]
    (t : A) (ht : Transcendental k t) :
    Set.Infinite (Set.range fun φ : A →ₐ[k] k ↦ φ t) := by
  intro hfinite
  let values := hfinite.toFinset
  let q : Polynomial k := values.prod fun c ↦ Polynomial.X - Polynomial.C c
  have hqne : q ≠ 0 :=
    (Polynomial.monic_prod_X_sub_C (fun c : k ↦ c) values).ne_zero
  have hqeval : Polynomial.aeval t q = 0 := by
    apply eq_zero_of_forall_character_eq_zero (k := k)
    intro φ
    rw [← Polynomial.aeval_algHom_apply φ t q]
    have hmem : φ t ∈ values := hfinite.mem_toFinset.mpr ⟨φ, rfl⟩
    simp only [q, map_prod, Polynomial.aeval_sub, Polynomial.aeval_X,
      Polynomial.aeval_C]
    exact Finset.prod_eq_zero hmem (sub_self _)
  apply hqne
  apply (transcendental_iff_injective.mp ht)
  simpa using hqeval

private lemma span_taylor_character_values_eq_top [IsDomain A]
    (t : A) (ht : Transcendental k t) (f : Polynomial k) (hf : f ≠ 0) :
    Ideal.span (Set.range fun φ : A →ₐ[k] k ↦ Polynomial.taylor (φ t) f) = ⊤ := by
  by_contra htop
  obtain ⟨J, hJmax, hle⟩ := Ideal.exists_le_maximal _ htop
  letI : J.IsMaximal := hJmax
  let ψ := characterOfMaximal (k := k) J
  let r : k := ψ Polynomial.X
  have hψ : ψ = Polynomial.aeval r := by
    apply Polynomial.algHom_ext
    simp [r]
  have hvanish : ∀ φ : A →ₐ[k] k,
      Polynomial.eval r (Polynomial.taylor (φ t) f) = 0 := by
    intro φ
    have hmem : Polynomial.taylor (φ t) f ∈ J :=
      hle (Ideal.subset_span (Set.mem_range_self φ))
    have hz := (characterOfMaximal_eq_zero_iff_mem (k := k) J _).mpr hmem
    change ψ (Polynomial.taylor (φ t) f) = 0 at hz
    rw [hψ] at hz
    simpa [Polynomial.aeval_def] using hz
  let values : Set k := Set.range fun φ : A →ₐ[k] k ↦ φ t
  have hvalues : values.Infinite := character_values_infinite (k := k) t ht
  have hshift : ((fun c : k ↦ r + c) '' values).Infinite :=
    hvalues.image (fun _ _ _ _ h ↦ add_left_cancel h)
  have hroots : Set.Infinite
      {x : k | Polynomial.eval x f = Polynomial.eval x (0 : Polynomial k)} := by
    apply hshift.mono
    rintro x ⟨c, ⟨φ, rfl⟩, rfl⟩
    have hz := hvanish φ
    rw [Polynomial.taylor_eval] at hz
    simpa using hz
  exact hf (Polynomial.eq_of_infinite_eval_eq f 0 hroots)

end Characters

section Main

variable {k : Type u} {A : Type v}
variable [Field k] [IsAlgClosed k] [CommRing A] [HopfAlgebra k A]
variable [IsDomain A] [Algebra.FiniteType k A]

/-- A primitive transcendental coordinate on a finite-type Hopf curve induces
a finite extension of its polynomial coordinate ring. -/
public theorem primitive_hopf_curve_aeval_finite
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0) :
    (Polynomial.aeval t : Polynomial k →ₐ[k] A).Finite := by
  classical
  rw [AlgHom.Finite, RingHom.Finite]
  letI : Algebra (Polynomial k) A :=
    (Polynomial.aeval t).toRingHom.toAlgebra
  letI : Algebra.FiniteType (Polynomial k) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (Polynomial k) A
  have halg : Algebra.IsAlgebraic (Polynomial k) A :=
    isAlgebraic_aeval_of_trdeg_eq_one t ht htrdeg
  letI : Algebra.IsAlgebraic (Polynomial k) A := halg
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := Polynomial k) (A := A)
  obtain ⟨f, hf, hint⟩ :=
    Algebra.IsAlgebraic.exists_integral_multiples (Polynomial k) s
  have hcomul : Coalgebra.comul (R := k) t =
      t ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] t :=
    (reducedComultiplication_eq_zero_iff (k := k) t).mp hprimitive
  let denoms : Set (Polynomial k) :=
    Set.range fun φ : A →ₐ[k] k ↦ Polynomial.taylor (φ t) f
  apply Module.Finite.of_localizationSpan denoms
    (span_taylor_character_values_eq_top (k := k) t ht f hf)
  intro g
  obtain ⟨φ, hφ⟩ := g.property
  rw [← hφ]
  let p : WithConv (A →ₐ[k] k) := WithConv.toConv φ
  let τ : A ≃ₐ[k] A := translationEquiv p
  let s' : Finset A := s.image τ
  apply finite_localizedModule_of_integral_multiples s'
  · simpa [s', τ] using adjoin_image_translation_eq_top p t hcomul s hs
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hcomp :
        (algebraMap (Polynomial k) A).comp
            (Polynomial.taylorEquiv (φ t)).toRingEquiv.toRingHom =
          τ.toRingEquiv.toRingHom.comp (algebraMap (Polynomial k) A) := by
      apply DFunLike.ext _ _
      intro q
      change Polynomial.aeval t (Polynomial.taylor (φ t) q) =
        translation p (Polynomial.aeval t q)
      simpa [p] using (translation_aeval_of_primitive p t hcomul q).symm
    have hmapped : IsIntegral (Polynomial k) (τ (f • x)) :=
      IsIntegral.map_of_comp_eq
        (Polynomial.taylorEquiv (φ t)).toRingEquiv.toRingHom
        τ.toRingEquiv.toRingHom hcomp (hint x hx)
    have htranslate_f :
        τ (algebraMap (Polynomial k) A f) =
          algebraMap (Polynomial k) A (Polynomial.taylor (φ t) f) := by
      change translation p (Polynomial.aeval t f) =
        Polynomial.aeval t (Polynomial.taylor (φ t) f)
      simpa [p] using translation_aeval_of_primitive p t hcomul f
    have hscaled : τ (f • x) = Polynomial.taylor (φ t) f • τ x := by
      simp only [Algebra.smul_def, map_mul]
      rw [htranslate_f]
    rw [hscaled] at hmapped
    exact hmapped

end Main

end Theory.AlgebraicGroup

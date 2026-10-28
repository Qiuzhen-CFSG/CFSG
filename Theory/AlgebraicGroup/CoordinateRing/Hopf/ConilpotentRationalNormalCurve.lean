module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.PrimitiveCurveFinite
public import Theory.FieldTheory.RationalFunctionInfiniteAffineTranslates

/-!
# Rational normal conilpotent Hopf curves

This module proves the normal rational case of the affine-line recovery used in
the coordinate-ring route to one-dimensional unipotent groups.  The input is a
normal finite-type Hopf domain of transcendence degree one, a transcendental
primitive coordinate `t`, and a rational generator of its fraction field.  The
result is an element `s` of the original ring with `A = k[s]`.

The proof follows the completion and one-boundary-point reduction in Borel,
*Linear Algebraic Groups*, Theorem 10.9
(`refs/KGroup/Bor1/Chapter3.tex`).  First,
`primitive_hopf_curve_aeval_finite` makes `A` finite over `k[t]`.  Characters of
the finite-type algebra give Hopf translations, which extend to automorphisms
of the fraction field and send `t` to `t + c`; the Nullstellensatz argument
shows that the set of such character values is infinite.  Rationality and
`rational_function_infinite_affine_translates_exists_one_place_parameter` then
give a fraction-field parameter `sK` for which `t` is polynomial.  Thus `sK` is
integral over `A`, so normality puts it in `A`.  Finally, finiteness over `k[t]`
and integral closedness of the polynomial ring `k[s]` inside the common
fraction field imply `A = k[s]`.

The ordered conilpotent-generator instance records the structural setting in
which this lower theorem is consumed.  Once the primitive coordinate and the
rationality witness are supplied, the argument proves the slightly stronger
fact that no further use of the chosen ordering is required.  In particular,
this module does not use any affine-line parameter owner, primitive-generator
classification, or polynomialization-data classification.
-/

universe u v

namespace Theory.AlgebraicGroup

set_option linter.style.haveILetI false

section NormalRecovery

variable {k : Type u} {A : Type v}
variable [Field k] [CommRing A] [Algebra k A] [IsDomain A]

private lemma normal_recovery_from_one_place
    (t : A) (hfinite : (Polynomial.aeval t : Polynomial k →ₐ[k] A).Finite)
    (s : A) (hs : Transcendental k s)
    (hfield : IntermediateField.adjoin k
      ({algebraMap A (FractionRing A) s} : Set (FractionRing A)) = ⊤)
    (ht : t ∈ Algebra.adjoin k ({s} : Set A)) :
    Algebra.adjoin k ({s} : Set A) = ⊤ := by
  classical
  let K := FractionRing A
  let iAK : A →ₐ[k] K := IsScalarTower.toAlgHom k A K
  let C := Algebra.adjoin k ({algebraMap A K s} : Set K)
  have hsurj : ∀ x : K, ∃ p q : C,
      x = algebraMap C K p / algebraMap C K q := by
    intro x
    have hx : x ∈ IntermediateField.adjoin k
        ({algebraMap A K s} : Set K) := by
      rw [hfield]
      trivial
    obtain ⟨r, hr, q, hq, hx⟩ := IntermediateField.mem_adjoin_iff_div.mp hx
    exact ⟨⟨r, hr⟩, ⟨q, hq⟩, hx⟩
  letI : IsFractionRing C K := IsFractionRing.of_field C K hsurj
  have hsK : Transcendental k (algebraMap A K s) := fun halg ↦
    hs ((isAlgebraic_algHom_iff iAK
      (FaithfulSMul.algebraMap_injective A K)).mp halg)
  let e : Polynomial k ≃ₐ[k] C :=
    Polynomial.algEquivOfTranscendental k (algebraMap A K s) hsK
  letI : IsIntegrallyClosed C := IsIntegrallyClosed.of_equiv e.toRingEquiv
  have htK : algebraMap A K t ∈ C := by
    change algebraMap A K t ∈
      Algebra.adjoin k ({algebraMap A K s} : Set K)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ht ⊢
    obtain ⟨p, hp⟩ := ht
    refine ⟨p, ?_⟩
    calc
      Polynomial.aeval (algebraMap A K s) p =
          iAK (Polynomial.aeval s p) :=
        Polynomial.aeval_algHom_apply iAK s p
      _ = iAK t := congrArg iAK hp
      _ = algebraMap A K t := rfl
  apply top_unique
  intro a _
  let tC : C := ⟨algebraMap A K t, htK⟩
  letI : Algebra (Polynomial k) A :=
    (Polynomial.aeval t : Polynomial k →ₐ[k] A).toRingHom.toAlgebra
  have ha : IsIntegral (Polynomial k) a := hfinite.to_isIntegral a
  have hcomp :
      (algebraMap C K).comp (Polynomial.aeval tC).toRingHom =
        (algebraMap A K).comp (algebraMap (Polynomial k) A) := by
    change (algebraMap C K).comp (Polynomial.aeval tC).toRingHom =
      (algebraMap A K).comp (Polynomial.aeval t).toRingHom
    apply Polynomial.ringHom_ext
    · intro x
      simpa using IsScalarTower.algebraMap_apply k A K x
    · simp [tC]
  have haC : IsIntegral C (algebraMap A K a) :=
    IsIntegral.map_of_comp_eq
      (Polynomial.aeval tC).toRingHom (algebraMap A K) hcomp ha
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp haC
  have haK : algebraMap A K a ∈ C := hc ▸ c.property
  change algebraMap A K a ∈
    Algebra.adjoin k ({algebraMap A K s} : Set K) at haK
  change a ∈ Algebra.adjoin k ({s} : Set A)
  rw [Algebra.adjoin_singleton_eq_range_aeval] at haK ⊢
  obtain ⟨p, hp⟩ := haK
  refine ⟨p, (FaithfulSMul.algebraMap_injective A K ?_)⟩
  calc
    algebraMap A K (Polynomial.aeval s p) =
        Polynomial.aeval (algebraMap A K s) p :=
      (Polynomial.aeval_algHom_apply iAK s p).symm
    _ = algebraMap A K a := hp

private lemma normal_recovery_from_fraction_parameter
    [IsIntegrallyClosed A]
    (t : A) (ht : Transcendental k t)
    (hfinite : (Polynomial.aeval t : Polynomial k →ₐ[k] A).Finite)
    (sK : FractionRing A) (hsK : Transcendental k sK)
    (hfield : IntermediateField.adjoin k ({sK} : Set (FractionRing A)) = ⊤)
    (htpoly : algebraMap A (FractionRing A) t ∈
      Algebra.adjoin k ({sK} : Set (FractionRing A))) :
    ∃ s : A, Transcendental k s ∧ Algebra.adjoin k ({s} : Set A) = ⊤ := by
  classical
  let K := FractionRing A
  let iAK : A →ₐ[k] K := IsScalarTower.toAlgHom k A K
  rw [Algebra.adjoin_singleton_eq_range_aeval] at htpoly
  obtain ⟨p, hp⟩ := htpoly
  change Polynomial.aeval sK p = algebraMap A K t at hp
  have htK : Transcendental k (algebraMap A K t) := fun halg ↦
    ht ((isAlgebraic_algHom_iff iAK
      (FaithfulSMul.algebraMap_injective A K)).mp halg)
  have hpdeg : p.natDegree ≠ 0 := by
    intro hdeg
    apply htK
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hp
    rw [← hp]
    simpa using isAlgebraic_algebraMap (A := K) (p.coeff 0)
  have hp0 : p ≠ 0 := fun hzero ↦ hpdeg (hzero ▸ Polynomial.natDegree_zero)
  let qk : Polynomial k := p * Polynomial.C p.leadingCoeff⁻¹
  have hqkmonic : qk.Monic := Polynomial.monic_mul_leadingCoeff_inv hp0
  have hqkdeg : qk.natDegree ≠ 0 := by
    simpa [qk, Polynomial.natDegree_mul_leadingCoeff_inv p hp0] using hpdeg
  let qA : Polynomial A := qk.map (algebraMap k A)
  have hqAmonic : qA.Monic := hqkmonic.map (algebraMap k A)
  have hqAdeg : qA.natDegree ≠ 0 := by
    change (qk.map (algebraMap k A)).natDegree ≠ 0
    rw [hqkmonic.natDegree_map]
    exact hqkdeg
  have hqeval : Polynomial.aeval sK qA =
      algebraMap A K (t * algebraMap k A p.leadingCoeff⁻¹) := by
    change Polynomial.aeval sK (qk.map (algebraMap k A)) = _
    rw [Polynomial.aeval_map_algebraMap]
    change Polynomial.aeval sK
      (p * Polynomial.C p.leadingCoeff⁻¹) = _
    rw [map_mul, Polynomial.aeval_C, hp]
    rw [map_mul, IsScalarTower.algebraMap_apply k A K]
  have hsKint : IsIntegral A sK :=
    IsIntegral.of_aeval_monic hqAmonic hqAdeg
      (hqeval ▸ isIntegral_algebraMap)
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp hsKint
  have hstrans : Transcendental k s := by
    intro halg
    apply hsK
    rw [← hs]
    exact halg.algHom iAK
  have hfield' : IntermediateField.adjoin k
      ({algebraMap A K s} : Set K) = ⊤ := by
    rw [hs]
    exact hfield
  have htpoly' : t ∈ Algebra.adjoin k ({s} : Set A) := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    refine ⟨p, (FaithfulSMul.algebraMap_injective A K ?_)⟩
    calc
      algebraMap A K (Polynomial.aeval s p) =
          Polynomial.aeval (algebraMap A K s) p :=
        (Polynomial.aeval_algHom_apply iAK s p).symm
      _ = Polynomial.aeval sK p := by rw [hs]
      _ = algebraMap A K t := hp
  refine ⟨s, hstrans, normal_recovery_from_one_place
    t hfinite s hstrans hfield' htpoly'⟩

end NormalRecovery

section Translation

variable {k : Type u} {A : Type v}
variable [Field k] [CommRing A] [HopfAlgebra k A]

private noncomputable def rationalCurveTranslation
    (p : WithConv (A →ₐ[k] k)) : A →ₐ[k] A :=
  (WithConv.toConv ((Algebra.ofId k A).comp p.ofConv) *
    WithConv.toConv (AlgHom.id k A)).ofConv

private lemma rationalCurveTranslation_mul (p q : WithConv (A →ₐ[k] k)) :
    (rationalCurveTranslation p).comp (rationalCurveTranslation q) =
      rationalCurveTranslation (q * p) := by
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
  simp only [rationalCurveTranslation, AlgHom.comp_convMul_distrib,
    WithConv.toConv_ofConv]
  rw [hscalar, hid]
  simp only [WithConv.toConv_ofConv, mul_assoc]

private lemma rationalCurveTranslation_one :
    rationalCurveTranslation (1 : WithConv (A →ₐ[k] k)) = AlgHom.id k A := by
  have hscalar :
      WithConv.toConv ((Algebra.ofId k A).comp
          (1 : WithConv (A →ₐ[k] k)).ofConv) =
        (1 : WithConv (A →ₐ[k] A)) := by
    apply WithConv.ofConv_injective
    ext x
    simp
  rw [rationalCurveTranslation, hscalar, one_mul]

private noncomputable def rationalCurveTranslationEquiv
    (p : WithConv (A →ₐ[k] k)) : A ≃ₐ[k] A :=
  AlgEquiv.ofAlgHom (rationalCurveTranslation p) (rationalCurveTranslation p⁻¹)
    (by rw [rationalCurveTranslation_mul]; simp [rationalCurveTranslation_one])
    (by rw [rationalCurveTranslation_mul]; simp [rationalCurveTranslation_one])

private lemma rationalCurveTranslation_apply_of_primitive
    (p : WithConv (A →ₐ[k] k)) (t : A)
    (ht : Coalgebra.comul (R := k) t =
      t ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] t) :
    rationalCurveTranslation p t = algebraMap k A (p t) + t := by
  rw [rationalCurveTranslation, AlgHom.convMul_apply, ht]
  simp

end Translation

section Characters

variable {k : Type u} {A : Type v}
variable [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
variable [Algebra.FiniteType k A]

private noncomputable def rationalCurveQuotientCharacter
    (J : Ideal A) [J.IsMaximal] : (A ⧸ J) →ₐ[k] k := by
  letI : Field (A ⧸ J) := Ideal.Quotient.field J
  letI : Algebra.FiniteType k (A ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k J)
      (Ideal.Quotient.mkₐ_surjective k J)
  letI : Module.Finite k (A ⧸ J) :=
    finite_of_finite_type_of_isJacobsonRing k (A ⧸ J)
  exact IsAlgClosed.lift

private noncomputable def rationalCurveCharacterOfMaximal
    (J : Ideal A) [J.IsMaximal] : A →ₐ[k] k :=
  (rationalCurveQuotientCharacter (k := k) J).comp (Ideal.Quotient.mkₐ k J)

private lemma rationalCurveCharacterOfMaximal_eq_zero_iff_mem
    (J : Ideal A) [J.IsMaximal] (a : A) :
    rationalCurveCharacterOfMaximal (k := k) J a = 0 ↔ a ∈ J := by
  letI : Field (A ⧸ J) := Ideal.Quotient.field J
  constructor
  · intro h
    have hq : Ideal.Quotient.mk J a = 0 :=
      (rationalCurveQuotientCharacter (k := k) J).injective
        (by simpa [rationalCurveCharacterOfMaximal] using h)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  · intro h
    have hq : Ideal.Quotient.mk J a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr h
    change rationalCurveQuotientCharacter (k := k) J
      (Ideal.Quotient.mk J a) = 0
    rw [hq, map_zero]

private lemma rationalCurve_eq_zero_of_forall_character_eq_zero
    [IsReduced A] (a : A) (ha : ∀ φ : A →ₐ[k] k, φ a = 0) : a = 0 := by
  letI : IsJacobsonRing A :=
    isJacobsonRing_of_finiteType (A := k) (B := A)
  have hjac : a ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson]
    apply Ideal.mem_sInf.mpr
    intro J hJ
    letI : J.IsMaximal := hJ.2
    exact (rationalCurveCharacterOfMaximal_eq_zero_iff_mem (k := k) J a).mp
      (ha (rationalCurveCharacterOfMaximal (k := k) J))
  rw [← Ideal.radical_eq_jacobson, Ideal.radical_bot_of_isReduced] at hjac
  exact Ideal.mem_bot.mp hjac

private lemma rationalCurve_character_values_infinite [IsDomain A]
    (t : A) (ht : Transcendental k t) :
    Set.Infinite (Set.range fun φ : A →ₐ[k] k ↦ φ t) := by
  intro hfinite
  let values := hfinite.toFinset
  let q : Polynomial k := values.prod fun c ↦ Polynomial.X - Polynomial.C c
  have hqne : q ≠ 0 :=
    (Polynomial.monic_prod_X_sub_C (fun c : k ↦ c) values).ne_zero
  have hqeval : Polynomial.aeval t q = 0 := by
    apply rationalCurve_eq_zero_of_forall_character_eq_zero (k := k)
    intro φ
    rw [← Polynomial.aeval_algHom_apply φ t q]
    have hmem : φ t ∈ values := hfinite.mem_toFinset.mpr ⟨φ, rfl⟩
    simp only [q, map_prod, Polynomial.aeval_sub, Polynomial.aeval_X,
      Polynomial.aeval_C]
    exact Finset.prod_eq_zero hmem (sub_self _)
  apply hqne
  apply (transcendental_iff_injective.mp ht)
  simpa using hqeval

end Characters

/-- A normal rational conilpotent Hopf curve with a primitive transcendental
coordinate admits a polynomial coordinate in its original affine ring. -/
public theorem normal_rational_conilpotent_hopf_curve_exists_affine_parameter
    {k : Type u} {A : Type v}
    [Field k] [IsAlgClosed k] [CommRing A] [HopfAlgebra k A]
    [IsDomain A] [Algebra.FiniteType k A] [IsIntegrallyClosed A]
    [HasOrderedConilpotentGenerators (k := k) (A := A)]
    (htrdeg : Algebra.trdeg k A = 1) (t : A)
    (ht : Transcendental k t)
    (hprimitive : reducedComultiplication (k := k) t = 0)
    (hrat : ∃ z : FractionRing A, Transcendental k z ∧
      IntermediateField.adjoin k ({z} : Set (FractionRing A)) = ⊤) :
    ∃ s : A, Transcendental k s ∧ Algebra.adjoin k ({s} : Set A) = ⊤ := by
  classical
  let K := FractionRing A
  let iAK : A →ₐ[k] K := IsScalarTower.toAlgHom k A K
  have hfinite : (Polynomial.aeval t : Polynomial k →ₐ[k] A).Finite :=
    primitive_hopf_curve_aeval_finite htrdeg t ht hprimitive
  have htK : Transcendental k (algebraMap A K t) := fun halg ↦
    ht ((isAlgebraic_algHom_iff iAK
      (FaithfulSMul.algebraMap_injective A K)).mp halg)
  have hcomul : Coalgebra.comul (R := k) t =
      t ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] t :=
    (reducedComultiplication_eq_zero_iff (k := k) t).mp hprimitive
  have hinfinite : Set.Infinite {c : k | ∃ sigma : K ≃ₐ[k] K,
      sigma (algebraMap A K t) =
        algebraMap A K t + algebraMap k K c} := by
    apply (rationalCurve_character_values_infinite (k := k) t ht).mono
    rintro c ⟨phi, rfl⟩
    let p : WithConv (A →ₐ[k] k) := WithConv.toConv phi
    let tauA : A ≃ₐ[k] A := rationalCurveTranslationEquiv p
    let tauK : K ≃ₐ[k] K :=
      IsFractionRing.algEquivOfAlgEquiv (K := K) (L := K) tauA
    refine ⟨tauK, ?_⟩
    calc
      tauK (algebraMap A K t) = algebraMap A K (tauA t) :=
        IsFractionRing.algEquivOfAlgEquiv_algebraMap tauA t
      _ = algebraMap A K (algebraMap k A (phi t) + t) := by
        rw [show tauA t = rationalCurveTranslation p t from rfl,
          rationalCurveTranslation_apply_of_primitive p t hcomul]
      _ = algebraMap A K t + algebraMap k K (phi t) := by
        rw [map_add, IsScalarTower.algebraMap_apply k A K]
        exact add_comm _ _
  obtain ⟨z, hz, hzgen⟩ := hrat
  obtain ⟨sK, hsK, hsKgen, htpoly⟩ :=
    rational_function_infinite_affine_translates_exists_one_place_parameter
      z (algebraMap A K t) hz hzgen htK hinfinite
  exact normal_recovery_from_fraction_parameter t ht hfinite sK hsK hsKgen htpoly

end Theory.AlgebraicGroup

module

public import Theory.AlgebraicGroup.CoordinateRing.Hopf.AdditivePolynomialComposition
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Polynomialization data and primitive-parameter elimination

This module isolates the algebraic output required from the normalization of a
smooth one-dimensional conilpotent Hopf algebra.  A
`ConilpotentCurvePolynomializationData` consists of a transcendental parameter
generating the algebra and a finite primitive augmentation-zero family written
as additive polynomials in that parameter.  Its positive-characteristic field
also records the stronger `p`-polynomial support obtained from additivity.

The main elimination argument proves that the parameter itself is primitive.
In positive characteristic, generation first forces a nonzero linear
coefficient and hence a separable family member.  Comparing evaluation maps on
the generated algebra proves that the common scalar zero locus is `{0}`.  The
Frobenius-Ore composition Bezout theorem then expresses `X` as a sum of
composites, and `p`-polynomials preserve primitive elements.  In characteristic
zero, the same derivative argument produces a nonzero linear additive
polynomial, from which the parameter is recovered by scalar multiplication.

This is the polynomial elimination step in the Hopf-coordinate proof of GLS
Proposition 1.3.5(c).  It deliberately does not infer polynomiality from
smoothness of an affine curve and does not choose a regular section of a
finite-kernel additive character.  Constructing the polynomialization data
from conilpotence is the separate geometric/Hopf input.
-/

open scoped TensorProduct Polynomial

namespace Theory.AlgebraicGroup

set_option linter.style.haveILetI false

universe u v w

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [HopfAlgebra k A]

/-- A polynomial coordinate together with a finite primitive additive family
which generates the same algebra. -/
public structure ConilpotentCurvePolynomializationData
    (k : Type u) (A : Type v) [Field k] [CommRing A] [HopfAlgebra k A] where
  parameter : A
  parameter_counit_zero : Coalgebra.counit (R := k) parameter = 0
  parameter_transcendental : Transcendental k parameter
  parameter_generates : Algebra.adjoin k {parameter} = ⊤
  count : ℕ
  polynomial : Fin count → Polynomial k
  additive : ∀ i, IsAdditivePolynomial (polynomial i)
  evaluated_counit_zero : ∀ i, Coalgebra.counit (R := k)
    (Polynomial.aeval parameter (polynomial i)) = 0
  evaluated_primitive : ∀ i, reducedComultiplication (k := k)
    (Polynomial.aeval parameter (polynomial i)) = 0
  evaluated_generates : Algebra.adjoin k
    (Set.range (fun i => Polynomial.aeval parameter (polynomial i))) = ⊤
  pPolynomial : ∀ (p : ℕ) [Fact p.Prime] [CharP k p] (i : Fin count),
    IsPPolynomial p (polynomial i)

private lemma pPolynomial_eval₂_add
    {p : ℕ} [Fact p.Prime] [CharP k p]
    {B : Type w} [CommRing B] [Algebra k B] [CharP B p]
    {f : Polynomial k} (hf : IsPPolynomial p f) (x y : B) :
  Polynomial.eval₂ (algebraMap k B) (x + y) f =
      Polynomial.eval₂ (algebraMap k B) x f +
        Polynomial.eval₂ (algebraMap k B) y f := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.eval₂_eq_sum,
    Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def,
    Polynomial.sum_def, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨i, rfl⟩ := (isPPolynomial_iff p f).mp hf n hn
  rw [add_pow_char_pow, mul_add]

/-- An additive polynomial has zero constant term. -/
public lemma additivePolynomial_eval_zero
    {f : Polynomial k} (hf : IsAdditivePolynomial f) : f.eval 0 = 0 := by
  have h := (isAdditivePolynomial_iff f).mp hf 0 0
  simp only [zero_add] at h
  apply add_left_cancel (a := f.eval 0)
  simpa using h.symm

/-- A `p`-polynomial has zero constant term. -/
public lemma pPolynomial_eval_zero
    {p : ℕ} [Fact p.Prime] [CharP k p]
    {f : Polynomial k} (hf : IsPPolynomial p f) : f.eval 0 = 0 :=
  additivePolynomial_eval_zero (pPolynomial_isAdditive p hf)

/-- Polynomial generators of `k[t]` have no common scalar zero except zero
when every generator has zero constant term. -/
public lemma polynomial_generators_common_zero
    {ι : Type*} {t : A} (ht : Transcendental k t)
    (htop : Algebra.adjoin k {t} = ⊤) (f : ι → Polynomial k)
    (hfzero : ∀ i, (f i).eval 0 = 0)
    (hgen : Algebra.adjoin k
      (Set.range (fun i => Polynomial.aeval t (f i))) = ⊤) (z : k) :
    (∀ i, (f i).eval z = 0) ↔ z = 0 := by
  have haeval_surj : Function.Surjective (Polynomial.aeval t : k[X] →ₐ[k] A) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
    exact htop
  let e : k[X] ≃ₐ[k] A := AlgEquiv.ofBijective (Polynomial.aeval t)
    ⟨transcendental_iff_injective.mp ht, haeval_surj⟩
  let ev (x : k) : A →ₐ[k] k := (Polynomial.aeval x).comp e.symm.toAlgHom
  have e_apply (q : k[X]) : e q = Polynomial.aeval t q := rfl
  constructor
  · intro hz
    have hev : ev z = ev 0 := by
      apply AlgHom.ext_of_adjoin_eq_top hgen
      rintro _ ⟨i, rfl⟩
      change Polynomial.aeval z (e.symm (Polynomial.aeval t (f i))) =
        Polynomial.aeval 0 (e.symm (Polynomial.aeval t (f i)))
      rw [← e_apply, e.symm_apply_apply]
      change (f i).eval z = (f i).eval 0
      exact (hz i).trans (hfzero i).symm
    have ht_eval := DFunLike.congr_fun hev t
    change Polynomial.aeval z (e.symm t) = Polynomial.aeval 0 (e.symm t) at ht_eval
    have eX : e Polynomial.X = t := by simp [e_apply]
    rw [← eX, e.symm_apply_apply, Polynomial.aeval_X,
      Polynomial.aeval_X] at ht_eval
    exact ht_eval
  · rintro rfl i
    exact hfzero i

private lemma additivePolynomial_derivative_eq_C_coeff_one
    [Infinite k] (f : Polynomial k) (hf : IsAdditivePolynomial f) :
    f.derivative = Polynomial.C (f.coeff 1) := by
  have hf' := (isAdditivePolynomial_iff f).mp hf
  have htranslate (z : k) :
      f.comp (Polynomial.X + Polynomial.C z) = Polynomial.C (f.eval z) + f := by
    apply Polynomial.funext
    intro x
    simpa [Polynomial.eval_comp, add_comm] using hf' z x
  have hderivative_translate (z : k) :
      f.derivative.comp (Polynomial.X + Polynomial.C z) = f.derivative := by
    have h := congrArg Polynomial.derivative (htranslate z)
    simpa [Polynomial.derivative_comp] using h
  have hconstant : f.derivative = Polynomial.C (f.derivative.eval 0) := by
    apply Polynomial.funext
    intro z
    have h := congrArg (Polynomial.eval 0) (hderivative_translate z)
    simpa [Polynomial.eval_comp] using h
  have hcoeff : f.derivative.eval 0 = f.coeff 1 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
    simp
  rw [hconstant, hcoeff]

/-- An additive-polynomial family generating `k[t]` contains a member with
nonzero linear coefficient.  Otherwise all derivatives vanish, and
differentiation of an algebraic expression for `t` in those generators
contradicts `X' = 1`. -/
public lemma additivePolynomial_generators_have_nonzero_linear_coefficient
    [Infinite k]
    {ι : Type*} {t : A} (ht : Transcendental k t)
    (htop : Algebra.adjoin k {t} = ⊤) (f : ι → Polynomial k)
    (hf : ∀ i, IsAdditivePolynomial (f i))
    (hgen : Algebra.adjoin k
      (Set.range (fun i => Polynomial.aeval t (f i))) = ⊤) :
    ∃ i, (f i).coeff 1 ≠ 0 := by
  have haeval_surj : Function.Surjective (Polynomial.aeval t : k[X] →ₐ[k] A) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
    exact htop
  let e : k[X] ≃ₐ[k] A := AlgEquiv.ofBijective (Polynomial.aeval t)
    ⟨transcendental_iff_injective.mp ht, haeval_surj⟩
  have e_apply (q : k[X]) : e q = Polynomial.aeval t q := rfl
  by_contra h
  push Not at h
  have htmem : t ∈ Algebra.adjoin k
      (Set.range (fun i => Polynomial.aeval t (f i))) := by
    rw [hgen]
    trivial
  have hderiv : (e.symm t).derivative = 0 := by
    refine Algebra.adjoin_induction (p := fun a _ => (e.symm a).derivative = 0)
      ?_ ?_ ?_ ?_ htmem
    · rintro _ ⟨i, rfl⟩
      change (e.symm (Polynomial.aeval t (f i))).derivative = 0
      rw [← e_apply, e.symm_apply_apply,
        additivePolynomial_derivative_eq_C_coeff_one (f i) (hf i), h i]
      simp
    · intro r
      change (e.symm (algebraMap k A r)).derivative = 0
      rw [e.symm.commutes]
      simp
    · intro x y _ _ hx hy
      rw [map_add, Polynomial.derivative_add, hx, hy, add_zero]
    · intro x y _ _ hx hy
      rw [map_mul, Polynomial.derivative_mul, hx, hy]
      simp
  have eX : e Polynomial.X = t := by simp [e_apply]
  rw [← eX, e.symm_apply_apply, Polynomial.derivative_X] at hderiv
  exact one_ne_zero hderiv

/-- A finite family of `p`-polynomials generating `k[t]` contains a separable
member. -/
public lemma pPolynomial_generators_have_separable_member
    [Infinite k] {p : ℕ} [Fact p.Prime] [CharP k p]
    {ι : Type*} {t : A} (ht : Transcendental k t)
    (htop : Algebra.adjoin k {t} = ⊤) (f : ι → Polynomial k)
    (hf : ∀ i, IsPPolynomial p (f i))
    (hgen : Algebra.adjoin k
      (Set.range (fun i => Polynomial.aeval t (f i))) = ⊤) :
    ∃ i, (f i).Separable := by
  obtain ⟨i, hi⟩ :=
    additivePolynomial_generators_have_nonzero_linear_coefficient ht htop f
      (fun i => pPolynomial_isAdditive p (hf i)) hgen
  refine ⟨i, (Polynomial.separable_def' (f i)).mpr ⟨0,
    Polynomial.C ((f i).coeff 1)⁻¹, ?_⟩⟩
  rw [additivePolynomial_derivative_eq_C_coeff_one
    (f i) (pPolynomial_isAdditive p (hf i))]
  rw [← Polynomial.C_mul, inv_mul_cancel₀ hi]
  simp

private lemma pPolynomial_aeval_tmul_one
    {B : Type w} [CommRing B] [Algebra k B]
    (f : Polynomial k) (x : B) :
    Polynomial.eval₂ (algebraMap k (B ⊗[k] B)) (x ⊗ₜ[k] (1 : B)) f =
      Polynomial.aeval x f ⊗ₜ[k] (1 : B) := by
  change Polynomial.eval₂ (algebraMap k (B ⊗[k] B))
      ((Algebra.TensorProduct.includeLeft (R := k) (S := k)
        (A := B) (B := B)) x) f =
    (Algebra.TensorProduct.includeLeft (R := k) (S := k)
      (A := B) (B := B)) (Polynomial.eval₂ (algebraMap k B) x f)
  change Polynomial.aeval
      ((Algebra.TensorProduct.includeLeft (R := k) (S := k)
        (A := B) (B := B)) x) f =
    (Algebra.TensorProduct.includeLeft (R := k) (S := k)
      (A := B) (B := B)) (Polynomial.aeval x f)
  exact Polynomial.aeval_algHom_apply _ _ _

private lemma pPolynomial_aeval_one_tmul
    {B : Type w} [CommRing B] [Algebra k B]
    (f : Polynomial k) (x : B) :
    Polynomial.eval₂ (algebraMap k (B ⊗[k] B)) ((1 : B) ⊗ₜ[k] x) f =
      (1 : B) ⊗ₜ[k] Polynomial.aeval x f := by
  change Polynomial.eval₂ (algebraMap k (B ⊗[k] B))
      ((Algebra.TensorProduct.includeRight (R := k)
        (A := B) (B := B)) x) f =
    (Algebra.TensorProduct.includeRight (R := k)
      (A := B) (B := B)) (Polynomial.eval₂ (algebraMap k B) x f)
  change Polynomial.aeval
      ((Algebra.TensorProduct.includeRight (R := k)
        (A := B) (B := B)) x) f =
    (Algebra.TensorProduct.includeRight (R := k)
      (A := B) (B := B)) (Polynomial.aeval x f)
  exact Polynomial.aeval_algHom_apply _ _ _

/-- A `p`-polynomial evaluated at a primitive element is primitive. -/
public lemma pPolynomial_aeval_reducedComultiplication_eq_zero
    [IsDomain A] {p : ℕ} [Fact p.Prime] [CharP k p]
    {f : Polynomial k} (hf : IsPPolynomial p f) {a : A}
    (ha : reducedComultiplication (k := k) a = 0) :
    reducedComultiplication (k := k) (Polynomial.aeval a f) = 0 := by
  letI : Nontrivial (A ⊗[k] A) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
      k A A (algebraMap k A).injective (algebraMap k A).injective
  letI : CharP (A ⊗[k] A) p :=
    charP_of_injective_algebraMap (algebraMap k (A ⊗[k] A)).injective p
  rw [reducedComultiplication_eq_zero_iff] at ha ⊢
  calc
    Coalgebra.comul (R := k) (Polynomial.aeval a f) =
        Polynomial.eval₂ (algebraMap k (A ⊗[k] A))
          (Coalgebra.comul (R := k) a) f := by
      change (Bialgebra.comulAlgHom k A) (Polynomial.aeval a f) =
        Polynomial.aeval ((Bialgebra.comulAlgHom k A) a) f
      exact (Polynomial.aeval_algHom_apply _ _ _).symm
    _ = Polynomial.eval₂ (algebraMap k (A ⊗[k] A))
          (a ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] a) f := by rw [ha]
    _ = Polynomial.eval₂ (algebraMap k (A ⊗[k] A))
          (a ⊗ₜ[k] (1 : A)) f +
        Polynomial.eval₂ (algebraMap k (A ⊗[k] A))
          ((1 : A) ⊗ₜ[k] a) f :=
      pPolynomial_eval₂_add hf _ _
    _ = Polynomial.aeval a f ⊗ₜ[k] (1 : A) +
        (1 : A) ⊗ₜ[k] Polynomial.aeval a f := by
      rw [pPolynomial_aeval_tmul_one, pPolynomial_aeval_one_tmul]

private lemma reducedComultiplication_add_eq_zero {a b : A}
    (ha : reducedComultiplication (k := k) a = 0)
    (hb : reducedComultiplication (k := k) b = 0) :
    reducedComultiplication (k := k) (a + b) = 0 := by
  rw [reducedComultiplication_eq_zero_iff] at ha hb ⊢
  simp only [map_add, ha, hb, TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

private lemma reducedComultiplication_smul_eq_zero (c : k) {a : A}
    (ha : reducedComultiplication (k := k) a = 0) :
    reducedComultiplication (k := k) (c • a) = 0 := by
  rw [reducedComultiplication_eq_zero_iff] at ha ⊢
  simp only [map_smul, ha]
  simp only [smul_add, TensorProduct.smul_tmul', TensorProduct.tmul_smul]

private lemma reducedComultiplication_sum_eq_zero
    {ι : Type*} (s : Finset ι) (a : ι → A)
    (ha : ∀ i ∈ s, reducedComultiplication (k := k) (a i) = 0) :
    reducedComultiplication (k := k) (∑ i ∈ s, a i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reducedComultiplication_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact reducedComultiplication_add_eq_zero
        (ha i (Finset.mem_insert_self i s))
        (ih fun j hj => ha j (Finset.mem_insert_of_mem hj))

/-- In characteristic zero, a finite additive-polynomial family generating
`k[t]` makes `t` primitive as soon as its evaluated members are primitive. -/
public theorem primitive_parameter_of_additivePolynomial_family
    [CharZero k] {ι : Type*} {t : A} (ht : Transcendental k t)
    (htop : Algebra.adjoin k {t} = ⊤) (f : ι → Polynomial k)
    (hf : ∀ i, IsAdditivePolynomial (f i))
    (hprimitive : ∀ i,
      reducedComultiplication (k := k) (Polynomial.aeval t (f i)) = 0)
    (hgen : Algebra.adjoin k
      (Set.range (fun i => Polynomial.aeval t (f i))) = ⊤) :
    reducedComultiplication (k := k) t = 0 := by
  obtain ⟨i, hi⟩ :=
    additivePolynomial_generators_have_nonzero_linear_coefficient ht htop f hf hgen
  have hne : f i ≠ 0 := fun hzero => hi (by rw [hzero]; simp)
  have hdegree : (f i).natDegree = 1 :=
    additivePolynomial_natDegree_eq_one (hf i) hne
  have hconst : (f i).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, additivePolynomial_eval_zero (hf i)]
  have hlinear : f i = Polynomial.C ((f i).coeff 1) * Polynomial.X := by
    simpa [hconst] using
      (Polynomial.eq_X_add_C_of_natDegree_le_one (p := f i) hdegree.le)
  have heval : Polynomial.aeval t (f i) = ((f i).coeff 1) • t := by
    rw [hlinear]
    simp [Algebra.smul_def]
  have hscaled : reducedComultiplication (k := k) (((f i).coeff 1) • t) = 0 := by
    rw [← heval]
    exact hprimitive i
  have hinv := reducedComultiplication_smul_eq_zero ((f i).coeff 1)⁻¹ hscaled
  simpa [smul_smul, inv_mul_cancel₀ hi] using hinv

/-- Genuine additive-polynomial composition Bezout elimination makes a
polynomial parameter primitive.  The family-generation hypothesis establishes
the common-zero condition rather than assuming it separately. -/
public theorem primitive_parameter_of_pPolynomial_family
    [IsAlgClosed k] [IsDomain A] {p : ℕ} [Fact p.Prime] [CharP k p]
    {ι : Type*} [Fintype ι] {t : A} (ht : Transcendental k t)
    (htop : Algebra.adjoin k {t} = ⊤) (f : ι → Polynomial k)
    (hf : ∀ i, IsPPolynomial p (f i))
    (hprimitive : ∀ i,
      reducedComultiplication (k := k) (Polynomial.aeval t (f i)) = 0)
    (hgen : Algebra.adjoin k
      (Set.range (fun i => Polynomial.aeval t (f i))) = ⊤) :
    reducedComultiplication (k := k) t = 0 := by
  have hzero : ∀ z : k, (∀ i, (f i).eval z = 0) ↔ z = 0 :=
    polynomial_generators_common_zero ht htop f
      (fun i => pPolynomial_eval_zero (hf i)) hgen
  obtain ⟨g, hg, hbezout⟩ :=
    pPolynomial_composition_bezout (p := p) f hf
      (pPolynomial_generators_have_separable_member ht htop f hf hgen) hzero
  have hsum :
      (∑ i, Polynomial.aeval (Polynomial.aeval t (f i)) (g i)) = t := by
    calc
      (∑ i, Polynomial.aeval (Polynomial.aeval t (f i)) (g i)) =
          ∑ i, Polynomial.aeval t ((g i).comp (f i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Polynomial.aeval_comp]
      _ = Polynomial.aeval t (∑ i, (g i).comp (f i)) := by rw [map_sum]
      _ = Polynomial.aeval t Polynomial.X := by rw [hbezout]
      _ = t := by simp
  rw [← hsum]
  exact reducedComultiplication_sum_eq_zero Finset.univ
    (fun i => Polynomial.aeval (Polynomial.aeval t (f i)) (g i))
    (fun i _ => pPolynomial_aeval_reducedComultiplication_eq_zero
      (hg i) (hprimitive i))

namespace ConilpotentCurvePolynomializationData

/-- The parameter in polynomialization data is primitive, in arbitrary
characteristic. -/
public theorem parameter_reducedComultiplication_eq_zero
    [IsAlgClosed k] [IsDomain A]
    (D : ConilpotentCurvePolynomializationData k A) :
    reducedComultiplication (k := k) D.parameter = 0 := by
  by_cases hchar : ringChar k = 0
  · letI : CharP k 0 := ringChar.of_eq hchar
    letI : CharZero k := CharP.charP_to_charZero k
    exact primitive_parameter_of_additivePolynomial_family
      D.parameter_transcendental D.parameter_generates D.polynomial
      D.additive D.evaluated_primitive D.evaluated_generates
  · let p : ℕ := ringChar k
    letI : CharP k p := by simpa [p] using ringChar.charP k
    have hpprime : p.Prime :=
      (CharP.char_is_prime_or_zero k p).resolve_right (by simpa [p] using hchar)
    letI : Fact p.Prime := ⟨hpprime⟩
    exact primitive_parameter_of_pPolynomial_family
      D.parameter_transcendental D.parameter_generates D.polynomial
      (D.pPolynomial p) D.evaluated_primitive D.evaluated_generates

/-- Polynomialization data supplies an augmentation-zero primitive generator
of the whole Hopf algebra. -/
public theorem exists_primitive_generator
    [IsAlgClosed k] [IsDomain A]
    (D : ConilpotentCurvePolynomializationData k A) :
    ∃ t : A, Coalgebra.counit (R := k) t = 0 ∧
      reducedComultiplication (k := k) t = 0 ∧
      Algebra.adjoin k {t} = ⊤ :=
  ⟨D.parameter, D.parameter_counit_zero,
    D.parameter_reducedComultiplication_eq_zero, D.parameter_generates⟩

end ConilpotentCurvePolynomializationData

end Theory.AlgebraicGroup

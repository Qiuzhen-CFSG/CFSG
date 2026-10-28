module

public import Theory.AlgebraicGroup.Unipotent.OneParameterCore
public import Theory.AlgebraicGroup.Unipotent.PrimitiveGenerator

/-!
# Additive structure from a polynomial coordinate

An affine algebraic group whose coordinate algebra is a polynomial ring in one
variable is isomorphic to the additive group. A normalized coordinate is
bijective on points by affine duality. Each right translation is an affine
linear polynomial, since its inverse is also polynomial. A nonunit slope would
have a fixed point, forcing that translation to be the identity; hence the
normalized coordinate is additive. Coordinate generation then gives a regular
inverse, using `PrimitiveAdditiveGeneratorData`.

This is the last step of Borel, Theorem 10.9 and its algebraic proof after
Corollary 11.6, and GLS Proposition 1.3.5(c). The coordinate-generation premise
is explicit here and must be established separately for a unipotent curve.
-/

open Theory.AlgebraicGroup

namespace Theory.AlgebraicGroup.AdditiveClassification

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {Y : Variety k} [AlgebraicGroup Y]

omit [AlgebraicGroup Y] in
private lemma parameter_bijective
    (s : Variety.PolynomialFunction Y) (hs : Transcendental k s)
    (hgen : Algebra.adjoin k {s} = ⊤) : Function.Bijective s := by
  have hsurj : Function.Surjective (Polynomial.aeval s : Polynomial k →ₐ[k]
      Variety.PolynomialFunction Y) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
    exact hgen
  let e : Polynomial k ≃ₐ[k] Variety.PolynomialFunction Y :=
    AlgEquiv.ofBijective (Polynomial.aeval s)
      ⟨transcendental_iff_injective.mp hs, hsurj⟩
  have heX : e Polynomial.X = s := Polynomial.aeval_X s
  constructor
  · intro x y hxy
    apply (polynomialFunctionPointAlgHomEquiv Y).injective
    apply AlgHom.ext_of_adjoin_eq_top hgen
    intro a ha
    obtain rfl : a = s := Set.mem_singleton_iff.mp ha
    exact hxy
  · intro c
    let φ : Variety.PolynomialFunction Y →ₐ[k] k :=
      (Polynomial.aeval c).comp e.symm.toAlgHom
    obtain ⟨x, hx, -⟩ := polynomialFunctionPointAlgHom_existsUnique Y φ
    refine ⟨x, ?_⟩
    change polynomialFunctionPointAlgHom Y x s = c
    rw [hx]
    change Polynomial.aeval c (e.symm s) = c
    rw [← heX, e.symm_apply_apply, Polynomial.aeval_X]

private lemma parameter_translate_affine
    (s : Variety.PolynomialFunction Y) (hs : Transcendental k s)
    (hgen : Algebra.adjoin k {s} = ⊤) (g : Variety.Point Y) :
    ∃ a b : k, a ≠ 0 ∧ ∀ x, s (x * g) = a * s x + b := by
  have hsurj : Function.Surjective (Polynomial.aeval s : Polynomial k →ₐ[k]
      Variety.PolynomialFunction Y) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
    exact hgen
  obtain ⟨P, hP⟩ := hsurj ((AlgebraicGroup.rightMulMorphism Y g).pullbackAlgHom s)
  obtain ⟨Q, hQ⟩ := hsurj ((AlgebraicGroup.rightMulMorphism Y g⁻¹).pullbackAlgHom s)
  have hPeval (x : Variety.Point Y) : P.eval (s x) = s (x * g) := by
    have h := congrArg (polynomialFunctionPointAlgHom Y x) hP
    rw [← Polynomial.aeval_algHom_apply] at h
    exact h
  have hQeval (x : Variety.Point Y) : Q.eval (s x) = s (x * g⁻¹) := by
    have h := congrArg (polynomialFunctionPointAlgHom Y x) hQ
    rw [← Polynomial.aeval_algHom_apply] at h
    exact h
  have hcomp : Q.comp P = Polynomial.X := by
    apply Polynomial.funext
    intro c
    obtain ⟨x, rfl⟩ := (parameter_bijective s hs hgen).2 c
    simp only [Polynomial.eval_comp, Polynomial.eval_X, hPeval, hQeval]
    rw [mul_inv_cancel_right]
  have hdeg : P.natDegree = 1 := by
    have hd : Q.natDegree * P.natDegree = 1 := by
      rw [← Polynomial.natDegree_comp, hcomp, Polynomial.natDegree_X]
    exact Nat.dvd_one.mp ⟨Q.natDegree, by simpa [mul_comm] using hd.symm⟩
  obtain ⟨a, ha, b, hshape⟩ := Polynomial.natDegree_eq_one.mp hdeg
  refine ⟨a, b, ha, fun x => ?_⟩
  rw [← hPeval, ← hshape]
  simp

/-- A polynomial coordinate on an algebraic group, normalized at its identity,
is additive. Right translations are affine automorphisms of the line; a
nontrivial affine slope would give a fixed point of a nontrivial translation. -/
private theorem parameter_additive
    (s : Variety.PolynomialFunction Y) (hs : Transcendental k s)
    (hgen : Algebra.adjoin k {s} = ⊤) (hsone : s 1 = 0) :
    ∀ x y : Variety.Point Y, s (x * y) = s x + s y := by
  have hb := parameter_bijective s hs hgen
  intro x g
  obtain ⟨a, b, ha, hformula⟩ := parameter_translate_affine s hs hgen g
  have hbval : b = s g := by simpa [hsone] using (hformula 1).symm
  subst b
  have haone : a = 1 := by
    by_contra hane
    have had : a - 1 ≠ 0 := sub_ne_zero.mpr hane
    obtain ⟨z, hz⟩ := hb.2 (-s g / (a - 1))
    have hfixed : z * g = z := by
      apply hb.1
      rw [hformula, hz]
      field_simp
      ring
    have hg : g = 1 := mul_left_cancel (hfixed.trans (mul_one z).symm)
    obtain ⟨w, hw⟩ := hb.2 1
    have h := hformula w
    rw [hg, mul_one, hsone, hw, mul_one, add_zero] at h
    exact hane h.symm
  rw [hformula, haone, one_mul]

/-- A transcendental singleton coordinate generator gives an actual additive
group parametrization, with regular inverse supplied by affine duality. -/
private theorem isOneParameter_of_normalized_polynomial_coordinate
    (s : Variety.PolynomialFunction Y) (hs : Transcendental k s)
    (hgen : Algebra.adjoin k {s} = ⊤) (hsone : s 1 = 0) :
    IsOneParameterGroup Y := by
  have hb := parameter_bijective s hs hgen
  let D : PrimitiveAdditiveGeneratorData Y :=
    { coordinate := s
      coordinate_one := hsone
      coordinate_mul := parameter_additive s hs hgen hsone
      coordinate_nontrivial := by
        obtain ⟨y, hy⟩ := hb.2 1
        exact ⟨y, hy ▸ one_ne_zero⟩
      generates := hgen }
  apply D.additiveGroupIso_of_surjective
  intro z
  obtain ⟨y, hy⟩ := hb.2 (z.val PUnit.unit)
  refine ⟨y, ?_⟩
  apply Variety.Point.ext
  funext i
  change s y = z.val i
  exact hy

/-- Every polynomial coordinate on an affine algebraic group can be normalized
at the identity to give an additive-group parametrization. -/
public theorem isOneParameter_of_polynomial_coordinate
    (s : Variety.PolynomialFunction Y) (hs : Transcendental k s)
    (hgen : Algebra.adjoin k {s} = ⊤) : IsOneParameterGroup Y := by
  let c : Variety.PolynomialFunction Y := algebraMap k _ (s 1)
  let t := s - c
  have htval (x : Variety.Point Y) : t x = s x - s 1 := by
    change s x - (algebraMap k (Variety.PolynomialFunction Y) (s 1)) x = _
    rw [polynomialFunction_algebraMap_apply]
  have hsurj : Function.Surjective t := by
    intro a
    obtain ⟨x, hx⟩ := (parameter_bijective s hs hgen).2 (a + s 1)
    exact ⟨x, by rw [htval, hx, add_sub_cancel_right]⟩
  have ht : Transcendental k t := by
    rw [transcendental_iff_injective]
    intro P Q hpq
    apply Polynomial.funext
    intro a
    obtain ⟨x, rfl⟩ := hsurj a
    have h := congrArg (polynomialFunctionPointAlgHom Y x) hpq
    simpa only [← Polynomial.aeval_algHom_apply, polynomialFunctionPointAlgHom_apply,
      Polynomial.coe_aeval_eq_eval] using h
  have htgen : Algebra.adjoin k {t} = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_le
    intro a ha
    rw [Set.mem_singleton_iff.mp ha]
    have hmem : t + c ∈ Algebra.adjoin k {t} :=
      (Algebra.adjoin k {t}).add_mem
        (Algebra.subset_adjoin (Set.mem_singleton t))
        ((Algebra.adjoin k {t}).algebraMap_mem (s 1))
    simpa [t] using hmem
  exact isOneParameter_of_normalized_polynomial_coordinate t ht htgen
    (by rw [htval, sub_self])

end Theory.AlgebraicGroup.AdditiveClassification

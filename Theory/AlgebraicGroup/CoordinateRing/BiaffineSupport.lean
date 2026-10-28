module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Theory.AlgebraicGroup.CoordinateRing.Point
public import Theory.AlgebraicGroup.Instance.Additive
public import Theory.AlgebraicGroup.Tori.Character.Point

/-!
# Biaffine additive-line support

This module identifies polynomial functions on the affine product of two copies
of the additive one-dimensional algebraic group with bivariate polynomials.
The source is written using `additiveGroupVariety`; the later `KPlus`
abbreviation unfolds to this variety, so the interface applies directly to
maps out of `Variety.prod (KPlus k) (KPlus k)` without importing the higher
unipotent layer.

The main support theorem centers a pulled-back target coordinate by subtracting
its value at `1`. If an algebraic-group morphism is trivial on both coordinate
axes, every nonzero monomial of the centered bivariate polynomial has positive
degree in both variables. The proof is purely coordinate-ring based: injectivity
of evaluation on the affine plane reduces the two axis restrictions to
univariate vanishing, then bivariate coefficients with one exponent equal to
zero are killed.

The final theorem adds the compatible torus-weight statement. Its hypothesis is
the coordinate-polynomial form of equivariance: scaling the two source
coordinates by the scalar point characters `alpha(t)` and `beta(t)` scales the
centered target coordinate by `gamma(t)`. Comparing coefficients then forces
each nonzero `(i,j)` coefficient to have character `gamma = alpha^i * beta^j`.
-/

universe u

namespace Theory.AlgebraicGroup

open scoped BigOperators

variable {k : Type u} [Field k]

@[expose]
public def additiveBiaffineEvalPoint (x y : k) : Fin 2 → k :=
  Fin.cases x (fun _ : Fin 1 => y)

omit [Field k] in
private lemma additiveBiaffineEvalPoint_zero (x y : k) :
    additiveBiaffineEvalPoint x y 0 = x :=
  rfl

omit [Field k] in
private lemma additiveBiaffineEvalPoint_one (x y : k) :
    additiveBiaffineEvalPoint x y 1 = y :=
  rfl

@[expose]
public def additiveLinePoint (t : k) :
    Variety.Point (additiveGroupVariety k) :=
  (additiveGroupPointEquiv k).symm (Multiplicative.ofAdd t)

@[expose]
public def additiveBiaffinePoint (x y : k) :
    Variety.Point (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)) :=
  ⟨Sum.elim (fun _ => x) (fun _ => y), by
    intro p hp
    simp [Variety.prod, additiveGroupVariety] at hp⟩

public lemma additiveBiaffinePoint_eq_prodPointEquiv_symm (x y : k) :
    additiveBiaffinePoint x y =
      (Variety.prodPointEquiv (additiveGroupVariety k) (additiveGroupVariety k)).symm
        (additiveLinePoint x, additiveLinePoint y) := by
  rfl

@[expose]
public def additiveBiaffineCoordinateEquiv :
    (additiveGroupVariety k).Coordinates ⊕
      (additiveGroupVariety k).Coordinates ≃ Fin 2 where
  toFun
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  invFun i := Fin.cases (Sum.inl PUnit.unit) (fun _ : Fin 1 => Sum.inr PUnit.unit) i
  left_inv := by
    intro i
    cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

public lemma additiveBiaffineEvaluationAlgHom_injective [IsAlgClosed k] :
    Function.Injective
      (evaluationAlgHom
        (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k))) := by
  intro p q hpq
  apply MvPolynomial.funext
  intro v
  let z : Variety.Point
      (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)) :=
    ⟨v, by
      intro r hr
      simp [Variety.prod, additiveGroupVariety] at hr⟩
  exact congrArg
    (fun F : Variety.PolynomialFunction
        (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)) => F z)
    hpq

@[expose]
public noncomputable def additiveBiaffinePolynomialFunctionAlgEquiv [IsAlgClosed k] :
    Variety.PolynomialFunction
        (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)) ≃ₐ[k]
      MvPolynomial (Fin 2) k := by
  have hF : Function.Bijective
      (evaluationAlgHom
        (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k))) :=
    ⟨additiveBiaffineEvaluationAlgHom_injective (k := k),
      evaluationRingHom_surjective
        (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k))⟩
  exact (AlgEquiv.ofBijective
    (evaluationAlgHom
      (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)))
    hF).symm.trans (MvPolynomial.renameEquiv k additiveBiaffineCoordinateEquiv)

public lemma additiveBiaffinePolynomialFunctionAlgEquiv_eval [IsAlgClosed k]
    (F : Variety.PolynomialFunction
      (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)))
    (x y : k) :
    MvPolynomial.eval (additiveBiaffineEvalPoint x y)
        (additiveBiaffinePolynomialFunctionAlgEquiv (k := k) F) =
      F (additiveBiaffinePoint x y) := by
  let E : MvPolynomial
        ((additiveGroupVariety k).Coordinates ⊕
          (additiveGroupVariety k).Coordinates) k ≃ₐ[k]
      Variety.PolynomialFunction
        (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)) :=
    AlgEquiv.ofBijective
      (evaluationAlgHom
        (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)))
      ⟨additiveBiaffineEvaluationAlgHom_injective (k := k),
        evaluationRingHom_surjective
          (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k))⟩
  let q : MvPolynomial
        ((additiveGroupVariety k).Coordinates ⊕
          (additiveGroupVariety k).Coordinates) k := E.symm F
  have h := congrArg
    (fun G : Variety.PolynomialFunction
        (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)) =>
      G (additiveBiaffinePoint x y))
    (E.apply_symm_apply F)
  change evalPolynomial (additiveBiaffinePoint x y).val q =
    F (additiveBiaffinePoint x y) at h
  calc
    MvPolynomial.eval (additiveBiaffineEvalPoint x y)
        (additiveBiaffinePolynomialFunctionAlgEquiv (k := k) F) =
        MvPolynomial.eval (additiveBiaffineEvalPoint x y)
          (MvPolynomial.rename additiveBiaffineCoordinateEquiv q) := by
      simp [additiveBiaffinePolynomialFunctionAlgEquiv, E, q]
    _ = evalPolynomial (additiveBiaffinePoint x y).val q := by
      rw [MvPolynomial.eval_rename]
      change MvPolynomial.eval
          (additiveBiaffineEvalPoint x y ∘ additiveBiaffineCoordinateEquiv) q =
        MvPolynomial.eval (additiveBiaffinePoint x y).val q
      have hfun :
          additiveBiaffineEvalPoint x y ∘ additiveBiaffineCoordinateEquiv =
            (additiveBiaffinePoint x y).val := by
        funext i
        cases i <;> rfl
      rw [hfun]
    _ = F (additiveBiaffinePoint x y) := h

@[expose]
public noncomputable def additiveBiaffineCenteredPullback
    {K : Variety k} [AlgebraicGroup K]
    (f : Variety.Morphism
      (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)) K)
    (q : Variety.PolynomialFunction K) :
    Variety.PolynomialFunction
      (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)) :=
  f.pullbackAlgHom q -
    algebraMap k
      (Variety.PolynomialFunction
        (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)))
      (q 1)

@[expose]
public noncomputable def additiveBiaffineCenteredPolynomial [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K]
    (f : Variety.Morphism
      (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)) K)
    (q : Variety.PolynomialFunction K) : MvPolynomial (Fin 2) k :=
  additiveBiaffinePolynomialFunctionAlgEquiv (k := k)
    (additiveBiaffineCenteredPullback f q)

public theorem additiveBiaffineCenteredPolynomial_eval [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K]
    (f : Variety.Morphism
      (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)) K)
    (q : Variety.PolynomialFunction K) (x y : k) :
    MvPolynomial.eval (additiveBiaffineEvalPoint x y)
        (additiveBiaffineCenteredPolynomial f q) =
      q (f.toFun (additiveBiaffinePoint x y)) - q 1 := by
  change MvPolynomial.eval (additiveBiaffineEvalPoint x y)
      (additiveBiaffinePolynomialFunctionAlgEquiv (k := k)
        (additiveBiaffineCenteredPullback f q)) =
    q (f.toFun (additiveBiaffinePoint x y)) - q 1
  rw [additiveBiaffinePolynomialFunctionAlgEquiv_eval (k := k)]
  dsimp [additiveBiaffineCenteredPullback]
  change q (f.toFun (additiveBiaffinePoint x y)) -
      (algebraMap k
        (Variety.PolynomialFunction
          (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)))
        (q 1)) (additiveBiaffinePoint x y) =
    q (f.toFun (additiveBiaffinePoint x y)) - q 1
  rw [polynomialFunction_algebraMap_apply]

@[expose]
public def additiveBiaffineMonomialWeight (a b : k) (m : Fin 2 →₀ ℕ) : k :=
  a ^ m 0 * b ^ m 1

@[expose]
public noncomputable def additiveBiaffineScalePolynomial (a b : k)
    (p : MvPolynomial (Fin 2) k) : MvPolynomial (Fin 2) k :=
  ∑ m ∈ p.support,
    MvPolynomial.monomial m
      (p.coeff m * additiveBiaffineMonomialWeight a b m)

public lemma additiveBiaffineScalePolynomial_coeff (a b : k)
    (p : MvPolynomial (Fin 2) k) (n : Fin 2 →₀ ℕ) :
    (additiveBiaffineScalePolynomial a b p).coeff n =
      p.coeff n * additiveBiaffineMonomialWeight a b n := by
  classical
  rw [additiveBiaffineScalePolynomial, MvPolynomial.coeff_sum]
  by_cases hn : n ∈ p.support
  · rw [Finset.sum_eq_single n]
    · simp [MvPolynomial.coeff_monomial]
    · intro m hm hmn
      simp [MvPolynomial.coeff_monomial, hmn]
    · intro hnnot
      contradiction
  · rw [Finset.sum_eq_zero]
    · rw [MvPolynomial.notMem_support_iff.mp hn]
      simp
    · intro m hm
      by_cases hmn : m = n
      · subst m
        contradiction
      · simp [MvPolynomial.coeff_monomial, hmn]

private lemma additiveBiaffineScalePolynomial_eval_monomial
    (a b x y c : k) (m : Fin 2 →₀ ℕ) :
    MvPolynomial.eval (additiveBiaffineEvalPoint x y)
      (MvPolynomial.monomial m
        (c * additiveBiaffineMonomialWeight a b m)) =
      MvPolynomial.eval (additiveBiaffineEvalPoint (a * x) (b * y))
        (MvPolynomial.monomial m c) := by
  rw [MvPolynomial.monomial_fin_two, MvPolynomial.monomial_fin_two]
  simp [additiveBiaffineEvalPoint_zero, additiveBiaffineEvalPoint_one,
    additiveBiaffineMonomialWeight, mul_pow]
  ring_nf

public lemma additiveBiaffineScalePolynomial_eval (a b x y : k)
    (p : MvPolynomial (Fin 2) k) :
    MvPolynomial.eval (additiveBiaffineEvalPoint x y)
      (additiveBiaffineScalePolynomial a b p) =
      MvPolynomial.eval (additiveBiaffineEvalPoint (a * x) (b * y)) p := by
  classical
  rw [additiveBiaffineScalePolynomial]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact additiveBiaffineScalePolynomial_eval_monomial a b x y (p.coeff m) m

private lemma TorusCharacter.pointCharacter_mul_apply
    {T : Variety k} [AlgebraicGroup T]
    (χ ψ : TorusCharacter T) (t : Variety.Point T) :
    (χ * ψ).pointCharacter t =
      χ.pointCharacter t * ψ.pointCharacter t := by
  change (dPointEquiv 1 ((χ * ψ).onPoints t) 0 : k) =
    (dPointEquiv 1 (χ.onPoints t) 0 : k) *
      (dPointEquiv 1 (ψ.onPoints t) 0 : k)
  change (dPointEquiv 1 (χ.onPoints t * ψ.onPoints t) 0 : k) =
    (dPointEquiv 1 (χ.onPoints t) 0 : k) *
      (dPointEquiv 1 (ψ.onPoints t) 0 : k)
  exact congrArg Units.val
    (congrFun (dPointEquiv_mul 1 (χ.onPoints t) (ψ.onPoints t)) 0)

private lemma TorusCharacter.pointCharacter_one_apply
    {T : Variety k} [AlgebraicGroup T] (t : Variety.Point T) :
    (1 : TorusCharacter T).pointCharacter t = 1 := by
  change (dPointEquiv 1 ((1 : TorusCharacter T).onPoints t) 0 : k) = 1
  change (dPointEquiv 1 (1 : Variety.Point (KMult k)) 0 : k) = 1
  exact congrArg Units.val (congrFun (dPointEquiv_one (k := k) 1) 0)

private lemma TorusCharacter.pointCharacter_pow_apply
    {T : Variety k} [AlgebraicGroup T]
    (χ : TorusCharacter T) (n : ℕ) (t : Variety.Point T) :
    (χ ^ n).pointCharacter t = χ.pointCharacter t ^ n := by
  induction n with
  | zero =>
      simpa using TorusCharacter.pointCharacter_one_apply (k := k) (T := T) t
  | succ n ih =>
      rw [pow_succ, TorusCharacter.pointCharacter_mul_apply, ih, pow_succ]

public theorem additiveBiaffine_coeff_character_of_scalePolynomial
    [IsAlgClosed k]
    {T : Variety k} [AlgebraicGroup T]
    (alpha beta gamma : TorusCharacter T)
    {p : MvPolynomial (Fin 2) k}
    (hscale : ∀ t : Variety.Point T,
      additiveBiaffineScalePolynomial
          (alpha.pointCharacter t) (beta.pointCharacter t) p =
        MvPolynomial.C (gamma.pointCharacter t) * p)
    {m : Fin 2 →₀ ℕ} (hm : p.coeff m ≠ 0) :
    gamma = alpha ^ (m 0) * beta ^ (m 1) := by
  apply TorusCharacter.pointCharacter_injective
  ext t
  have hcoeff :=
    congrArg (fun P : MvPolynomial (Fin 2) k => P.coeff m) (hscale t)
  rw [additiveBiaffineScalePolynomial_coeff, MvPolynomial.coeff_C_mul] at hcoeff
  have hval : gamma.pointCharacter t =
      alpha.pointCharacter t ^ m 0 * beta.pointCharacter t ^ m 1 := by
    apply mul_left_cancel₀ hm
    calc
      p.coeff m * gamma.pointCharacter t =
          gamma.pointCharacter t * p.coeff m := by
        rw [mul_comm]
      _ =
          p.coeff m *
            (alpha.pointCharacter t ^ m 0 * beta.pointCharacter t ^ m 1) := by
        rw [← hcoeff]
        rw [additiveBiaffineMonomialWeight]
  simpa [TorusCharacter.pointCharacter_mul_apply,
    TorusCharacter.pointCharacter_pow_apply] using hval

public theorem additiveBiaffine_coeff_character_of_eval_scaling
    [IsAlgClosed k]
    {T : Variety k} [AlgebraicGroup T]
    (alpha beta gamma : TorusCharacter T)
    {p : MvPolynomial (Fin 2) k}
    (hscale : ∀ (t : Variety.Point T) (x y : k),
      MvPolynomial.eval
        (additiveBiaffineEvalPoint (alpha.pointCharacter t * x)
          (beta.pointCharacter t * y)) p =
        gamma.pointCharacter t *
          MvPolynomial.eval (additiveBiaffineEvalPoint x y) p)
    {m : Fin 2 →₀ ℕ} (hm : p.coeff m ≠ 0) :
    gamma = alpha ^ (m 0) * beta ^ (m 1) := by
  apply additiveBiaffine_coeff_character_of_scalePolynomial
    (alpha := alpha) (beta := beta) (gamma := gamma) (p := p)
  · intro t
    apply MvPolynomial.funext
    intro v
    have hv : additiveBiaffineEvalPoint (v 0) (v 1) = v := by
      funext i
      fin_cases i <;> rfl
    calc
      MvPolynomial.eval v
          (additiveBiaffineScalePolynomial (alpha.pointCharacter t)
            (beta.pointCharacter t) p) =
          MvPolynomial.eval (additiveBiaffineEvalPoint (v 0) (v 1))
            (additiveBiaffineScalePolynomial (alpha.pointCharacter t)
              (beta.pointCharacter t) p) := by
        rw [hv]
      _ = MvPolynomial.eval
          (additiveBiaffineEvalPoint (alpha.pointCharacter t * v 0)
            (beta.pointCharacter t * v 1)) p := by
        rw [additiveBiaffineScalePolynomial_eval]
      _ = gamma.pointCharacter t *
          MvPolynomial.eval (additiveBiaffineEvalPoint (v 0) (v 1)) p :=
        hscale t (v 0) (v 1)
      _ = MvPolynomial.eval v (MvPolynomial.C (gamma.pointCharacter t) * p) := by
        rw [hv]
        simp
  · exact hm

private def axisLeft (y : k) : Fin 2 → k :=
  additiveBiaffineEvalPoint 0 y

private def axisRight (x : k) : Fin 2 → k :=
  additiveBiaffineEvalPoint x 0

private lemma coeff_eq_zero_of_left_axis_zero [IsAlgClosed k]
    {p : MvPolynomial (Fin 2) k}
    (h : ∀ y : k, MvPolynomial.eval (axisLeft y) p = 0)
    {m : Fin 2 →₀ ℕ} (hm0 : m 0 = 0) :
    p.coeff m = 0 := by
  let P : MvPolynomial (Fin 1) k :=
    Polynomial.coeff (MvPolynomial.finSuccEquiv k 1 p) 0
  have hP : P = 0 := by
    apply MvPolynomial.funext
    intro y
    have hy := h (y 0)
    have hy' : MvPolynomial.eval (Fin.cons (0 : k) y) p = 0 := by
      have hfun : axisLeft (y 0) = Fin.cons (0 : k) y := by
        funext i
        fin_cases i <;> rfl
      simpa [hfun] using hy
    rw [MvPolynomial.eval_eq_eval_mv_eval'] at hy'
    rw [← Polynomial.coeff_zero_eq_eval_zero] at hy'
    simpa [P, Polynomial.coeff_map] using hy'
  have hcoeff := congrArg (fun q : MvPolynomial (Fin 1) k => q.coeff m.tail) hP
  dsimp [P] at hcoeff
  rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hcoeff
  have hmtail : m.tail.cons 0 = m := by
    rw [show (0 : ℕ) = m 0 by exact hm0.symm]
    exact Finsupp.cons_tail m
  rw [hmtail] at hcoeff
  simpa using hcoeff

private def finTwoSwap : Fin 2 ≃ Fin 2 :=
  Equiv.swap 0 1

private lemma axisLeft_swap (x : k) :
    axisLeft x ∘ finTwoSwap = axisRight x := by
  funext i
  fin_cases i <;> rfl

private lemma coeff_eq_zero_of_right_axis_zero [IsAlgClosed k]
    {p : MvPolynomial (Fin 2) k}
    (h : ∀ x : k, MvPolynomial.eval (axisRight x) p = 0)
    {m : Fin 2 →₀ ℕ} (hm1 : m 1 = 0) :
    p.coeff m = 0 := by
  have hleft : ∀ x : k,
      MvPolynomial.eval (axisLeft x) (MvPolynomial.rename finTwoSwap p) = 0 := by
    intro x
    rw [MvPolynomial.eval_rename]
    simpa [axisLeft_swap] using h x
  have hzero := coeff_eq_zero_of_left_axis_zero (k := k) hleft
    (m := m.mapDomain finTwoSwap) (by
      rw [Finsupp.mapDomain_equiv_apply]
      simpa [finTwoSwap] using hm1)
  have hcoeff :=
    (MvPolynomial.coeff_rename_mapDomain finTwoSwap finTwoSwap.injective p m)
  rw [hcoeff] at hzero
  exact hzero

private lemma mixed_support_of_axes [IsAlgClosed k]
    {p : MvPolynomial (Fin 2) k}
    (hleft : ∀ y : k, MvPolynomial.eval (axisLeft y) p = 0)
    (hright : ∀ x : k, MvPolynomial.eval (axisRight x) p = 0)
    {m : Fin 2 →₀ ℕ} (hm : m ∈ p.support) :
    0 < m 0 ∧ 0 < m 1 := by
  constructor
  · by_contra h0
    have hm0 : m 0 = 0 := Nat.eq_zero_of_not_pos h0
    have hcoeff := coeff_eq_zero_of_left_axis_zero (k := k) hleft hm0
    exact (MvPolynomial.mem_support_iff.mp hm) hcoeff
  · by_contra h1
    have hm1 : m 1 = 0 := Nat.eq_zero_of_not_pos h1
    have hcoeff := coeff_eq_zero_of_right_axis_zero (k := k) hright hm1
    exact (MvPolynomial.mem_support_iff.mp hm) hcoeff

public theorem additiveBiaffine_axis_mixed_polynomial_support [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K]
    (f : Variety.Morphism
      (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)) K)
    (q : Variety.PolynomialFunction K)
    (hleft : ∀ y : k, f.toFun (additiveBiaffinePoint 0 y) = 1)
    (hright : ∀ x : k, f.toFun (additiveBiaffinePoint x 0) = 1) :
    ∀ m ∈ (additiveBiaffineCenteredPolynomial f q).support,
      0 < m 0 ∧ 0 < m 1 := by
  let F : Variety.PolynomialFunction
      (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)) :=
    additiveBiaffineCenteredPullback f q
  let p : MvPolynomial (Fin 2) k :=
    additiveBiaffineCenteredPolynomial f q
  have hleftPoly : ∀ y : k, MvPolynomial.eval (axisLeft y) p = 0 := by
    intro y
    have hev := additiveBiaffinePolynomialFunctionAlgEquiv_eval (k := k) F 0 y
    change MvPolynomial.eval (axisLeft y) p = 0
    rw [show axisLeft y = additiveBiaffineEvalPoint 0 y by rfl]
    change MvPolynomial.eval (additiveBiaffineEvalPoint 0 y)
      (additiveBiaffinePolynomialFunctionAlgEquiv (k := k) F) = 0
    rw [show MvPolynomial.eval (additiveBiaffineEvalPoint 0 y)
        (additiveBiaffinePolynomialFunctionAlgEquiv (k := k) F) =
        F (additiveBiaffinePoint 0 y) by
      simpa [additiveBiaffineEvalPoint] using hev]
    dsimp [F]
    change q (f.toFun (additiveBiaffinePoint 0 y)) -
        (algebraMap k
          (Variety.PolynomialFunction
            (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)))
          (q 1)) (additiveBiaffinePoint 0 y) = 0
    rw [polynomialFunction_algebraMap_apply]
    rw [hleft y]
    simp
  have hrightPoly : ∀ x : k, MvPolynomial.eval (axisRight x) p = 0 := by
    intro x
    have hev := additiveBiaffinePolynomialFunctionAlgEquiv_eval (k := k) F x 0
    change MvPolynomial.eval (axisRight x) p = 0
    rw [show axisRight x = additiveBiaffineEvalPoint x 0 by rfl]
    change MvPolynomial.eval (additiveBiaffineEvalPoint x 0)
      (additiveBiaffinePolynomialFunctionAlgEquiv (k := k) F) = 0
    rw [show MvPolynomial.eval (additiveBiaffineEvalPoint x 0)
        (additiveBiaffinePolynomialFunctionAlgEquiv (k := k) F) =
        F (additiveBiaffinePoint x 0) by
      simpa [additiveBiaffineEvalPoint] using hev]
    dsimp [F]
    change q (f.toFun (additiveBiaffinePoint x 0)) -
        (algebraMap k
          (Variety.PolynomialFunction
            (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)))
          (q 1)) (additiveBiaffinePoint x 0) = 0
    rw [polynomialFunction_algebraMap_apply]
    rw [hright x]
    simp
  intro m hm
  exact mixed_support_of_axes (k := k) hleftPoly hrightPoly hm

public theorem additiveBiaffine_axis_mixed_weight_polynomial_support [IsAlgClosed k]
    {K T : Variety k} [AlgebraicGroup K] [AlgebraicGroup T]
    (f : Variety.Morphism
      (Variety.prod (additiveGroupVariety k) (additiveGroupVariety k)) K)
    (q : Variety.PolynomialFunction K)
    (alpha beta gamma : TorusCharacter T)
    (hleft : ∀ y : k, f.toFun (additiveBiaffinePoint 0 y) = 1)
    (hright : ∀ x : k, f.toFun (additiveBiaffinePoint x 0) = 1)
    (hscale : ∀ (t : Variety.Point T) (x y : k),
      MvPolynomial.eval
        (additiveBiaffineEvalPoint (alpha.pointCharacter t * x)
          (beta.pointCharacter t * y))
        (additiveBiaffineCenteredPolynomial f q) =
        gamma.pointCharacter t *
          MvPolynomial.eval (additiveBiaffineEvalPoint x y)
            (additiveBiaffineCenteredPolynomial f q)) :
    ∀ m ∈ (additiveBiaffineCenteredPolynomial f q).support,
      0 < m 0 ∧ 0 < m 1 ∧ gamma = alpha ^ (m 0) * beta ^ (m 1) := by
  intro m hm
  have hmixed :=
    additiveBiaffine_axis_mixed_polynomial_support
      (k := k) f q hleft hright m hm
  have hcoeff : (additiveBiaffineCenteredPolynomial f q).coeff m ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  have hchar :=
    additiveBiaffine_coeff_character_of_eval_scaling
      (k := k) alpha beta gamma hscale hcoeff
  exact ⟨hmixed.1, hmixed.2, hchar⟩

end Theory.AlgebraicGroup

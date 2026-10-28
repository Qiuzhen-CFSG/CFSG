module

public import Theory.AlgebraicGroup.CoordinateRing.Hopf.AdditivePolynomialDegree
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.EraseLead
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.FieldTheory.Perfect

/-!
# Polynomial Artin--Schreier cocycles

This module records the polynomial cochains for the additive line in a
structured bivariate representation.  The substitution `X ↦ X + Y` is made
by `Polynomial.eval₂`, so all evaluations used below are evaluations of actual
polynomials rather than informal coefficient notation.  The straightening
theorem proves the characteristic-`p` cohomological input: every normalized
symmetric additive two-cocycle satisfying the Artin--Schreier equation is
itself a coboundary, and the residual one-variable polynomial is additive.
The separate elimination theorem then removes the higher Frobenius powers
recursively while keeping the correcting polynomial additive.  Its maximal
degree step subtracts `h^p - h`, cancels the leading term, and uses algebraic
closure to choose a `p`-th root of the leading coefficient.

The cocycle hypotheses are kept in the public interface so consumers can
transport them from Hopf-coordinate calculations.  The polynomial cohomology
certificate is proved internally by differentiating the cocycle identity,
taking coefficientwise Frobenius roots, and descending on outer polynomial
degree.  No geometric primitive-curve classification is used.

Source provenance: this is the pure polynomial step isolated from the
characteristic-`p` primitive Hopf-curve argument.  The Artin--Schreier
compatibility is essential in the derivative reduction and at every recursive
Frobenius-root step; the proof does not assert that an arbitrary normalized
symmetric additive two-cocycle is a coboundary.
-/

open scoped Polynomial Polynomial.Bivariate

namespace Theory.AlgebraicGroup

noncomputable section

universe u
variable {k : Type u} [Field k]

/-- The structured ring of polynomials in two additive-line coordinates. -/
public abbrev BivariatePolynomial (k : Type u) [Semiring k] := Polynomial (Polynomial k)

/-- The first coordinate inclusion. -/
public noncomputable def bivariateLeft (f : Polynomial k) : BivariatePolynomial k :=
  Polynomial.C f

/-- The second coordinate inclusion. -/
public noncomputable def bivariateRight (f : Polynomial k) : BivariatePolynomial k :=
  f.map (Polynomial.C : k →+* Polynomial k)

/-- Substitution of `X + Y` into a one-variable polynomial. -/
public def bivariateAddSub (f : Polynomial k) : BivariatePolynomial k :=
  f.eval₂ ((Polynomial.C : Polynomial k →+* BivariatePolynomial k).comp
      (Polynomial.C : k →+* Polynomial k))
    ((Polynomial.C (R := Polynomial k) Polynomial.X) +
      (Polynomial.X : BivariatePolynomial k))

/-- The additive coboundary `δ f(X,Y) = f(X+Y)-f(X)-f(Y)`. -/
public def additiveCoboundary (f : Polynomial k) : BivariatePolynomial k :=
  bivariateAddSub f - bivariateLeft f - bivariateRight f

public lemma bivariateLeft_eval (f : Polynomial k) (x y : k) :
    (bivariateLeft f).evalEval x y = f.eval x := by
  exact Polynomial.evalEval_C x y f

public lemma bivariateRight_eval (f : Polynomial k) (x y : k) :
    (bivariateRight f).evalEval x y = f.eval y := by
  exact Polynomial.evalEval_map_C x y f

public lemma bivariateAddSub_eval (f : Polynomial k) (x y : k) :
    (bivariateAddSub f).evalEval x y = f.eval (x + y) := by
  induction f using Polynomial.induction_on with
  | C a => simp [bivariateAddSub, Polynomial.evalEval]
  | add p q hp hq =>
      rw [bivariateAddSub] at hp hq ⊢
      rw [Polynomial.eval₂_add, Polynomial.evalEval_add, hp, hq,
        Polynomial.eval_add]
  | monomial n a _ =>
      simp [bivariateAddSub, Polynomial.evalEval]

public lemma additiveCoboundary_eval (f : Polynomial k) (x y : k) :
    (additiveCoboundary f).evalEval x y =
      f.eval (x + y) - f.eval x - f.eval y := by
  simp only [additiveCoboundary, Polynomial.evalEval_sub]
  rw [bivariateLeft_eval, bivariateRight_eval, bivariateAddSub_eval]

public def IsNormalizedPolynomialCocycle (C : BivariatePolynomial k) : Prop :=
  (∀ y : k, C.evalEval 0 y = 0) ∧ (∀ x : k, C.evalEval x 0 = 0)

public def IsSymmetricPolynomialCocycle (C : BivariatePolynomial k) : Prop :=
  ∀ x y : k, C.evalEval x y = C.evalEval y x

public def IsAdditivePolynomialTwoCocycle (C : BivariatePolynomial k) : Prop :=
  ∀ x y z : k,
    C.evalEval x y + C.evalEval (x + y) z =
          C.evalEval y z + C.evalEval x (y + z)

public lemma isNormalizedPolynomialCocycle_iff (C : BivariatePolynomial k) :
    IsNormalizedPolynomialCocycle C ↔
      (∀ y : k, C.evalEval 0 y = 0) ∧ (∀ x : k, C.evalEval x 0 = 0) :=
  Iff.rfl

public lemma isSymmetricPolynomialCocycle_iff (C : BivariatePolynomial k) :
    IsSymmetricPolynomialCocycle C ↔
      ∀ x y : k, C.evalEval x y = C.evalEval y x :=
  Iff.rfl

public lemma isAdditivePolynomialTwoCocycle_iff (C : BivariatePolynomial k) :
    IsAdditivePolynomialTwoCocycle C ↔
      ∀ x y z : k,
        C.evalEval x y + C.evalEval (x + y) z =
          C.evalEval y z + C.evalEval x (y + z) :=
  Iff.rfl

public lemma additiveCoboundary_zero :
    additiveCoboundary (0 : Polynomial k) = 0 := by
  simp [additiveCoboundary, bivariateAddSub, bivariateLeft, bivariateRight]

private lemma additiveCoboundary_pow_eval
    {p : ℕ} [Fact p.Prime] [CharP k p]
    (f : Polynomial k) (x y : k) :
    ((additiveCoboundary f) ^ p).evalEval x y =
      (f.eval (x + y)) ^ p - (f.eval x) ^ p - (f.eval y) ^ p := by
  rw [Polynomial.evalEval_pow, additiveCoboundary_eval]
  rw [show f.eval (x + y) - f.eval x - f.eval y =
      (f.eval (x + y) + -f.eval x) + -f.eval y by ring]
  calc
    (f.eval (x + y) + -f.eval x + -f.eval y) ^ p =
        (f.eval (x + y) + -f.eval x) ^ p + (-f.eval y) ^ p := by
          simpa only [pow_one] using
            add_pow_char_pow (f.eval (x + y) + -f.eval x) (-f.eval y) p 1
    _ = ((f.eval (x + y)) ^ p + (-f.eval x) ^ p) + (-f.eval y) ^ p := by
          rw [show (f.eval (x + y) + -f.eval x) ^ p =
              (f.eval (x + y)) ^ p + (-f.eval x) ^ p by
            simpa only [pow_one] using
              add_pow_char_pow (f.eval (x + y)) (-f.eval x) p 1]
    _ = _ := by
      have hneg (a : k) : (-a) ^ p = -a ^ p := by
        rw [neg_pow, neg_one_pow_char, neg_one_mul]
      rw [hneg (f.eval x), hneg (f.eval y)]
      ring

private lemma additiveCoboundary_straightened_is_additive
    {p : ℕ} [Fact p.Prime] [CharP k p]
    {C : BivariatePolynomial k} {f h : Polynomial k}
    (hC : C = additiveCoboundary h)
    (hartin : C ^ p - C = additiveCoboundary f) :
    IsAdditivePolynomial (f - (h ^ p - h)) := by
  rw [isAdditivePolynomial_iff]
  intro x y
  have heq := congrArg
    (fun Q : BivariatePolynomial k => Q.evalEval x y) hartin
  rw [hC] at heq
  rw [Polynomial.evalEval_sub, additiveCoboundary_pow_eval] at heq
  rw [additiveCoboundary_eval h x y] at heq
  rw [additiveCoboundary_eval f x y] at heq
  simp only [Polynomial.eval_sub, Polynomial.eval_pow]
  linear_combination -heq

private lemma bivariateAddSub_derivative (F : Polynomial k) :
    (bivariateAddSub F).derivative = bivariateAddSub F.derivative := by
  rw [show bivariateAddSub F =
      (F.map (Polynomial.C : k →+* Polynomial k)).eval₂
        (Polynomial.C : Polynomial k →+* BivariatePolynomial k)
        ((Polynomial.C (R := Polynomial k) Polynomial.X) +
          (Polynomial.X : BivariatePolynomial k)) by
    rw [Polynomial.eval₂_map]
    rfl]
  rw [Polynomial.derivative_eval₂_C]
  rw [Polynomial.derivative_add, Polynomial.derivative_C,
    Polynomial.derivative_X, zero_add, mul_one]
  rw [Polynomial.derivative_map]
  have hsub := (Polynomial.eval₂_map (p := F.derivative)
      (f := (Polynomial.C : k →+* Polynomial k))
      (g := (Polynomial.C : Polynomial k →+* BivariatePolynomial k))
      (x := (Polynomial.C (R := Polynomial k) Polynomial.X) +
        (Polynomial.X : BivariatePolynomial k)))
  simpa [bivariateAddSub] using hsub

private lemma bivariateRight_derivative (F : Polynomial k) :
    (bivariateRight F).derivative = bivariateRight F.derivative := by
  dsimp [bivariateRight]
  rw [Polynomial.derivative_map]

private lemma additiveCoboundary_derivative (F : Polynomial k) :
    (additiveCoboundary F).derivative =
      bivariateAddSub F.derivative - bivariateRight F.derivative := by
  simp only [additiveCoboundary, Polynomial.derivative_sub,
    bivariateAddSub_derivative, bivariateLeft, Polynomial.derivative_C,
    bivariateRight_derivative]
  abel

private lemma bivariate_ext [Infinite k] {A B : BivariatePolynomial k}
    (h : ∀ x y : k, A.evalEval x y = B.evalEval x y) : A = B := by
  apply Polynomial.ext
  intro n
  apply Polynomial.funext
  intro x
  have hpoly : A.map (Polynomial.evalRingHom x) =
      B.map (Polynomial.evalRingHom x) := by
    apply Polynomial.funext
    intro y
    rw [Polynomial.map_evalRingHom_eval, Polynomial.map_evalRingHom_eval]
    exact h x y
  have hc := congrArg (fun Q : Polynomial k => Q.coeff n) hpoly
  simpa using hc

private lemma bivariate_pow_injective {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] {A B : BivariatePolynomial k} (h : A ^ p = B ^ p) : A = B := by
  apply bivariate_ext
  intro x y
  have hxy := congrArg (fun Q : BivariatePolynomial k => Q.evalEval x y) h
  have hxy' := injective_frobenius k p (by
    simpa [frobenius_def] using hxy)
  simpa [Polynomial.evalEval_pow] using hxy'

private def evalLeft (C : BivariatePolynomial k) (x : k) : Polynomial k :=
  C.map (Polynomial.evalRingHom x)

private lemma evalLeft_eval (C : BivariatePolynomial k) (x y : k) :
    (evalLeft C x).eval y = C.evalEval x y :=
  Polynomial.map_evalRingHom_eval x y C

private lemma evalLeft_derivative (C : BivariatePolynomial k) (x : k) :
    (evalLeft C x).derivative = evalLeft C.derivative x :=
  Polynomial.derivative_map C (Polynomial.evalRingHom x)

private lemma cocycle_poly [Infinite k] {C : BivariatePolynomial k}
    (hc : IsAdditivePolynomialTwoCocycle C) (x y : k) :
    Polynomial.C (C.evalEval x y) + evalLeft C (x + y) =
      evalLeft C y + (evalLeft C x).comp (Polynomial.X + Polynomial.C y) := by
  apply Polynomial.funext
  intro z
  simpa [evalLeft_eval, Polynomial.eval_comp, add_comm] using
    (isAdditivePolynomialTwoCocycle_iff C).mp hc x y z

private lemma cocycle_derivative_eval_zero [Infinite k] {C : BivariatePolynomial k}
    (hc : IsAdditivePolynomialTwoCocycle C) (x y : k) :
    (C.derivative).evalEval x y =
      (C.derivative).evalEval (x + y) 0 - (C.derivative).evalEval y 0 := by
  have h := congrArg Polynomial.derivative (cocycle_poly hc x y)
  have h0 := congrArg (fun q : Polynomial k => q.eval 0) h
  rw [Polynomial.derivative_add, Polynomial.derivative_C,
    Polynomial.derivative_add, Polynomial.derivative_comp,
    Polynomial.derivative_X_add_C] at h0
  simp only [evalLeft_derivative, evalLeft_eval, Polynomial.eval_add,
    zero_add, one_mul,
    Polynomial.eval_comp, Polynomial.eval_X, Polynomial.eval_C] at h0
  linear_combination -h0

private lemma cocycle_derivative_eq_addSub_sub_right
    {C : BivariatePolynomial k} [Infinite k]
    (hc : IsAdditivePolynomialTwoCocycle C) :
    C.derivative = bivariateAddSub (C.coeff 1) - bivariateRight (C.coeff 1) := by
  apply Polynomial.ext
  intro i
  apply Polynomial.funext
  intro x
  have hp : evalLeft C.derivative x =
      evalLeft (bivariateAddSub (C.coeff 1) - bivariateRight (C.coeff 1)) x := by
    apply Polynomial.funext
    intro y
    have h := cocycle_derivative_eval_zero hc x y
    have hd0 : C.derivative.coeff 0 = C.coeff 1 := by
      ext j
      simp [Polynomial.coeff_derivative]
    have heval (t : k) : C.derivative.evalEval t 0 =
        (C.coeff 1).eval t := by
      rw [Polynomial.evalEval, Polynomial.C_0,
        ← Polynomial.coeff_zero_eq_eval_zero, hd0]
    simpa [evalLeft_eval, bivariateAddSub_eval, bivariateRight_eval,
      Polynomial.eval_sub, heval] using h
  have hi := congrArg (fun q : Polynomial k => q.coeff i) hp
  simpa [evalLeft, Polynomial.coeff_map] using hi

private lemma bivariate_pow_derivative_zero
    {p : ℕ} [Fact p.Prime] [CharP k p]
    (D : BivariatePolynomial k) : (D ^ p).derivative = 0 := by
  rw [Polynomial.derivative_pow]
  have hp : (p : BivariatePolynomial k) = 0 := by
    have hk : (p : k) = 0 :=
      (CharP.cast_eq_zero_iff k p p).mpr (dvd_refl p)
    change Polynomial.C (p : Polynomial k) = 0
    rw [Polynomial.C_eq_zero]
    change Polynomial.C (p : k) = 0
    rw [hk, map_zero]
  rw [Polynomial.C_eq_natCast, hp, zero_mul, zero_mul]

private def rootPoly {p : ℕ} (a : Polynomial k) [Fact p.Prime]
    [CharP k p] [IsAlgClosed k] : Polynomial k :=
  (a.contract p).map (frobeniusEquiv k p).symm

private lemma rootPoly_pow {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (a : Polynomial k) (ha : a.derivative = 0) :
    (rootPoly (p := p) a) ^ p = a := by
  rw [rootPoly, ← polynomial_expand_eq k p (a.contract p)]
  rw [Polynomial.expand_contract p ha (Fact.out : p.Prime).ne_zero]

private lemma rootPoly_zero {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k] :
    rootPoly (p := p) (0 : Polynomial k) = 0 := by
  have hcontract : (0 : Polynomial k).contract p = 0 := by
    ext n
    rw [Polynomial.coeff_contract (Fact.out : p.Prime).ne_zero]
    exact Polynomial.coeff_zero _
  rw [rootPoly, hcontract]
  exact Polynomial.map_zero _

private def rootBiv {p : ℕ} (A : BivariatePolynomial k) [Fact p.Prime]
    [CharP k p] [IsAlgClosed k] : BivariatePolynomial k :=
  A.sum (fun n a => Polynomial.C (rootPoly (p := p) a) * Polynomial.X ^ n)

private lemma rootBiv_monomial {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (n : ℕ) (a : Polynomial k) (ha : a.derivative = 0) :
    (rootBiv (p := p) (Polynomial.monomial n a)) ^ p =
      Polynomial.expand (Polynomial k) p (Polynomial.monomial n a) := by
  rw [rootBiv, Polynomial.sum_monomial_index]
  · rw [mul_pow, ← Polynomial.C_pow, rootPoly_pow a ha]
    rw [Polynomial.expand_monomial, ← pow_mul,
      ← Polynomial.C_mul_X_pow_eq_monomial]
  · simp [rootPoly_zero]

private lemma rootBiv_expand {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (A : BivariatePolynomial k)
    (hA : ∀ n, (A.coeff n).derivative = 0) :
    (rootBiv (p := p) A) ^ p = Polynomial.expand (Polynomial k) p A := by
  rw [rootBiv, Polynomial.sum_def]
  have hpow :
      (∑ n ∈ A.support,
        Polynomial.C (rootPoly (p := p) (A.coeff n)) * Polynomial.X ^ n) ^ p =
      ∑ n ∈ A.support,
        (Polynomial.C (rootPoly (p := p) (A.coeff n)) * Polynomial.X ^ n) ^ p := by
    induction A.support using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty,
          zero_pow (Fact.out : p.Prime).ne_zero]
    | @insert n s hn ih =>
        rw [Finset.sum_insert hn, Finset.sum_insert hn]
        calc
          (Polynomial.C (rootPoly (p := p) (A.coeff n)) * Polynomial.X ^ n +
              ∑ x ∈ s, Polynomial.C (rootPoly (p := p) (A.coeff x)) * Polynomial.X ^ x) ^ p =
              (Polynomial.C (rootPoly (p := p) (A.coeff n)) * Polynomial.X ^ n) ^ p +
                (∑ x ∈ s, Polynomial.C (rootPoly (p := p) (A.coeff x)) * Polynomial.X ^ x) ^ p := by
                simpa only [pow_one] using
                  add_pow_char_pow
                    (Polynomial.C (rootPoly (p := p) (A.coeff n)) * Polynomial.X ^ n)
                    (∑ x ∈ s, Polynomial.C (rootPoly (p := p) (A.coeff x)) * Polynomial.X ^ x) p 1
          _ = (Polynomial.C (rootPoly (p := p) (A.coeff n)) * Polynomial.X ^ n) ^ p +
                ∑ x ∈ s, (Polynomial.C (rootPoly (p := p) (A.coeff x)) * Polynomial.X ^ x) ^ p := by
                rw [ih]
  rw [hpow]
  conv_rhs => rw [← A.sum_monomial_eq]
  rw [Polynomial.sum_def, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hterm := rootBiv_monomial (p := p) n (A.coeff n) (hA n)
  simpa [rootBiv, Polynomial.sum_monomial_index, rootPoly_zero,
    Polynomial.expand_monomial] using hterm

private lemma exists_bivariate_pth_root {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] {C : BivariatePolynomial k}
    (houter : C.derivative = 0)
    (hinner : ∀ n, (C.coeff n).derivative = 0) :
    ∃ E : BivariatePolynomial k, E ^ p = C := by
  let A : BivariatePolynomial k := C.contract p
  have hA : ∀ n, ((A.coeff n) : Polynomial k).derivative = 0 := by
    intro n
    dsimp [A]
    rw [Polynomial.coeff_contract (Fact.out : p.Prime).ne_zero]
    exact hinner (n * p)
  refine ⟨rootBiv (p := p) A, ?_⟩
  rw [rootBiv_expand A hA]
  exact Polynomial.expand_contract p houter (Fact.out : p.Prime).ne_zero

private lemma pth_root_cocycle {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] {E C : BivariatePolynomial k} (hpow : E ^ p = C)
    (hc : IsAdditivePolynomialTwoCocycle C) :
    IsAdditivePolynomialTwoCocycle E := by
  rw [isAdditivePolynomialTwoCocycle_iff]
  intro x y z
  apply (frobeniusEquiv k p).injective
  change
    (E.evalEval x y + E.evalEval (x + y) z) ^ p =
      (E.evalEval y z + E.evalEval x (y + z)) ^ p
  have h := (isAdditivePolynomialTwoCocycle_iff C).mp hc x y z
  rw [← hpow] at h
  rw [Polynomial.evalEval_pow, Polynomial.evalEval_pow,
    Polynomial.evalEval_pow, Polynomial.evalEval_pow] at h
  rw [show (E.evalEval x y + E.evalEval (x + y) z) ^ p =
      E.evalEval x y ^ p + E.evalEval (x + y) z ^ p by
        simpa only [pow_one] using add_pow_char_pow _ _ p 1,
    show (E.evalEval y z + E.evalEval x (y + z)) ^ p =
      E.evalEval y z ^ p + E.evalEval x (y + z) ^ p by
        simpa only [pow_one] using add_pow_char_pow _ _ p 1]
  exact h

private lemma pth_root_normalized {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] {E C : BivariatePolynomial k} (hpow : E ^ p = C)
    (hn : IsNormalizedPolynomialCocycle C) :
    IsNormalizedPolynomialCocycle E := by
  rw [isNormalizedPolynomialCocycle_iff]
  have hn' := (isNormalizedPolynomialCocycle_iff C).mp hn
  constructor <;> intro x
  · apply (frobeniusEquiv k p).injective
    change (E.evalEval 0 x) ^ p = (0 : k) ^ p
    have hzero := hn'.1 x
    rw [← hpow, Polynomial.evalEval_pow] at hzero
    simpa [zero_pow (Fact.out : p.Prime).ne_zero] using hzero
  · apply (frobeniusEquiv k p).injective
    change (E.evalEval x 0) ^ p = (0 : k) ^ p
    have hzero := hn'.2 x
    rw [← hpow, Polynomial.evalEval_pow] at hzero
    simpa [zero_pow (Fact.out : p.Prime).ne_zero] using hzero

private lemma pth_root_symmetric {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] {E C : BivariatePolynomial k} (hpow : E ^ p = C)
    (hs : IsSymmetricPolynomialCocycle C) :
    IsSymmetricPolynomialCocycle E := by
  rw [isSymmetricPolynomialCocycle_iff]
  have hs' := (isSymmetricPolynomialCocycle_iff C).mp hs
  intro x y
  apply (frobeniusEquiv k p).injective
  change (E.evalEval x y) ^ p = (E.evalEval y x) ^ p
  have hsym := hs' x y
  rw [← hpow, Polynomial.evalEval_pow, Polynomial.evalEval_pow] at hsym
  exact hsym

private lemma additiveCoboundary_additive_linear [IsAlgClosed k] (a : k) :
    additiveCoboundary (Polynomial.C a * Polynomial.X) = 0 := by
  apply bivariate_ext
  intro x y
  rw [additiveCoboundary_eval]
  simp [Polynomial.eval_mul]
  ring

private lemma additiveCoboundary_add [IsAlgClosed k] (f g : Polynomial k) :
    additiveCoboundary (f + g) = additiveCoboundary f + additiveCoboundary g := by
  apply bivariate_ext
  intro x y
  rw [Polynomial.evalEval_add, additiveCoboundary_eval,
    additiveCoboundary_eval, additiveCoboundary_eval]
  simp [Polynomial.eval_add]
  ring

private lemma additiveCoboundary_sub [IsAlgClosed k] (f g : Polynomial k) :
    additiveCoboundary (f - g) = additiveCoboundary f - additiveCoboundary g := by
  apply bivariate_ext
  intro x y
  rw [Polynomial.evalEval_sub, additiveCoboundary_eval,
    additiveCoboundary_eval, additiveCoboundary_eval]
  simp [Polynomial.eval_sub]
  ring

private lemma normalized_sub {A B : BivariatePolynomial k}
    (hA : IsNormalizedPolynomialCocycle A)
    (hB : IsNormalizedPolynomialCocycle B) :
    IsNormalizedPolynomialCocycle (A - B) := by
  rw [isNormalizedPolynomialCocycle_iff] at hA hB ⊢
  constructor <;> intro x
  · simpa [Polynomial.evalEval_sub] using congrArg id (sub_eq_zero.mpr (by
      rw [hA.1 x, hB.1 x]))
  · simpa [Polynomial.evalEval_sub] using congrArg id (sub_eq_zero.mpr (by
      rw [hA.2 x, hB.2 x]))

private lemma symmetric_sub {A B : BivariatePolynomial k}
    (hA : IsSymmetricPolynomialCocycle A)
    (hB : IsSymmetricPolynomialCocycle B) :
    IsSymmetricPolynomialCocycle (A - B) := by
  rw [isSymmetricPolynomialCocycle_iff] at hA hB ⊢
  intro x y
  rw [Polynomial.evalEval_sub, hA x y, hB x y]
  rw [Polynomial.evalEval_sub]

private lemma cocycle_sub {A B : BivariatePolynomial k}
    (hA : IsAdditivePolynomialTwoCocycle A)
    (hB : IsAdditivePolynomialTwoCocycle B) :
    IsAdditivePolynomialTwoCocycle (A - B) := by
  rw [isAdditivePolynomialTwoCocycle_iff] at hA hB ⊢
  intro x y z
  simp only [Polynomial.evalEval_sub]
  linear_combination hA x y z - hB x y z

private lemma pth_root_natDegree_lt {p n : ℕ} [Fact p.Prime]
    {E R : BivariatePolynomial k} (hpow : E ^ p = R)
    (hR : R.natDegree ≤ n) (hn : 1 ≤ n) :
    E.natDegree + 1 < n + 1 := by
  by_cases hE : E = 0
  · simp [hE]
    omega
  have hdeg : p * E.natDegree = R.natDegree := by
    rw [← hpow, Polynomial.natDegree_pow]
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hmult : 2 * E.natDegree ≤ p * E.natDegree :=
    Nat.mul_le_mul_right E.natDegree hp
  omega

private lemma additiveCoboundary_pow {p : ℕ} [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] (f : Polynomial k) :
    additiveCoboundary (f ^ p) = (additiveCoboundary f) ^ p := by
  apply bivariate_ext
  intro x y
  rw [additiveCoboundary_eval, Polynomial.evalEval_pow,
    additiveCoboundary_eval]
  simp only [Polynomial.eval_pow]
  rw [show f.eval (x + y) - f.eval x - f.eval y =
      (f.eval (x + y) + -f.eval x) + -f.eval y by ring]
  symm
  calc
    (f.eval (x + y) + -f.eval x + -f.eval y) ^ p =
        (f.eval (x + y) + -f.eval x) ^ p + (-f.eval y) ^ p := by
          simpa only [pow_one] using
            add_pow_char_pow (f.eval (x + y) + -f.eval x) (-f.eval y) p 1
    _ = ((f.eval (x + y)) ^ p + (-f.eval x) ^ p) + (-f.eval y) ^ p := by
          rw [show (f.eval (x + y) + -f.eval x) ^ p =
              (f.eval (x + y)) ^ p + (-f.eval x) ^ p by
            simpa only [pow_one] using
              add_pow_char_pow (f.eval (x + y)) (-f.eval x) p 1]
    _ = _ := by
      have hneg (a : k) : (-a) ^ p = -a ^ p := by
        rw [neg_pow, neg_one_pow_char, neg_one_mul]
      rw [hneg (f.eval x), hneg (f.eval y)]
      ring

private lemma additiveCoboundary_derivative_zero_root
    {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    {D : BivariatePolynomial k} {f : Polynomial k}
    (h : D ^ p = additiveCoboundary f) :
    ∃ g : Polynomial k, D = additiveCoboundary g := by
  have hder := congrArg Polynomial.derivative h
  have hpowderiv := bivariate_pow_derivative_zero (p := p) D
  rw [hpowderiv, additiveCoboundary_derivative] at hder
  have hsubright : bivariateAddSub f.derivative =
      bivariateRight f.derivative := sub_eq_zero.mp hder.symm
  have hfder : f.derivative = Polynomial.C (f.derivative.eval 0) := by
    apply Polynomial.funext
    intro x
    have hx := congrArg (fun Q : BivariatePolynomial k => Q.evalEval x 0) hsubright
    rw [bivariateAddSub_eval, bivariateRight_eval] at hx
    simpa using hx
  let c : k := f.derivative.eval 0
  let r : Polynomial k := f - Polynomial.C c * Polynomial.X
  have hrder : r.derivative = 0 := by
    dsimp [r]
    rw [Polynomial.derivative_sub, hfder, Polynomial.derivative_C_mul,
      Polynomial.derivative_X]
    simp [c]
  let g : Polynomial k := rootPoly (p := p) r
  have hrg : g ^ p = r := by
    simpa [g] using rootPoly_pow r hrder
  have hdeltaf : additiveCoboundary f = additiveCoboundary r := by
    rw [show f = r + Polynomial.C c * Polynomial.X by
      dsimp [r]
      abel, additiveCoboundary_add, additiveCoboundary_additive_linear,
      add_zero]
  have hpowdelta := additiveCoboundary_pow (p := p) g
  have hpow : D ^ p = (additiveCoboundary g) ^ p := by
    rw [h, hdeltaf, ← hrg, hpowdelta]
  refine ⟨g, ?_⟩
  exact bivariate_pow_injective hpow

private lemma additiveCoboundary_symmetric (f : Polynomial k) :
    IsSymmetricPolynomialCocycle (additiveCoboundary f) := by
  rw [isSymmetricPolynomialCocycle_iff]
  intro x y
  rw [additiveCoboundary_eval, additiveCoboundary_eval]
  ring_nf

private lemma additiveCoboundary_normalized (f : Polynomial k)
    (hf0 : f.eval 0 = 0) : IsNormalizedPolynomialCocycle (additiveCoboundary f) := by
  rw [isNormalizedPolynomialCocycle_iff]
  constructor <;> intro x
  · rw [additiveCoboundary_eval]
    simp [hf0]
  · rw [additiveCoboundary_eval]
    simp [hf0]

private lemma additiveCoboundary_cocycle (f : Polynomial k) :
    IsAdditivePolynomialTwoCocycle (additiveCoboundary f) := by
  rw [isAdditivePolynomialTwoCocycle_iff]
  intro x y z
  repeat rw [additiveCoboundary_eval]
  ring_nf

private def formalIntegral (d : Polynomial k) : Polynomial k :=
  d.sum fun n a => Polynomial.C (a / (n + 1 : k)) * Polynomial.X ^ (n + 1)

private lemma formalIntegral_eval_zero (d : Polynomial k) :
    (formalIntegral d).eval 0 = 0 := by
  rw [formalIntegral, Polynomial.eval_sum, Polynomial.sum_def]
  apply Finset.sum_eq_zero
  intro n hn
  simp [Polynomial.eval_mul]

private lemma derivative_formalIntegral {d : Polynomial k}
    (hd : ∀ n : ℕ, (n + 1 : k) = 0 → d.coeff n = 0) :
    (formalIntegral d).derivative = d := by
  rw [formalIntegral, Polynomial.sum_def, Polynomial.derivative_sum]
  conv_rhs => rw [← d.sum_monomial_eq]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Polynomial.derivative_C_mul_X_pow]
  simp only [Nat.cast_add, Nat.cast_one]
  by_cases hzero : (n + 1 : k) = 0
  · simp [hd n hzero, hzero]
  · rw [div_mul_cancel₀ _ hzero]
    rw [Polynomial.C_mul_X_pow_eq_monomial]
    simp

private lemma formalIntegral_natDegree_le (d : Polynomial k) :
    (formalIntegral d).natDegree ≤ d.natDegree + 1 := by
  rw [formalIntegral, Polynomial.sum_def]
  apply (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := d.natDegree + 1))
  intro n hn
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
    (Nat.add_le_add_right (Polynomial.le_natDegree_of_mem_supp n hn) 1)

private lemma derivative_reduction
    {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    {C : BivariatePolynomial k} {f : Polynomial k}
    (_hcocycle : IsAdditivePolynomialTwoCocycle C)
    (hartin : C ^ p - C = additiveCoboundary f) :
    ∃ h : Polynomial k, h = formalIntegral (C.coeff 1) ∧
      C.derivative = (additiveCoboundary h).derivative := by
  have hder := congrArg Polynomial.derivative hartin
  rw [Polynomial.derivative_sub, bivariate_pow_derivative_zero,
    additiveCoboundary_derivative] at hder
  have hcder := cocycle_derivative_eq_addSub_sub_right _hcocycle
  have hzero : bivariateAddSub (C.coeff 1 + f.derivative) =
      bivariateRight (C.coeff 1 + f.derivative) := by
    apply bivariate_ext
    intro x y
    have hderxy := congrArg (fun Q : BivariatePolynomial k => Q.evalEval x y) hder
    have hcderxy := congrArg (fun Q : BivariatePolynomial k => Q.evalEval x y) hcder
    rw [Polynomial.evalEval_sub] at hderxy
    rw [Polynomial.evalEval_sub] at hcderxy
    simp only [Polynomial.evalEval_sub] at hderxy hcderxy
    rw [bivariateAddSub_eval, bivariateRight_eval] at hderxy hcderxy
    rw [bivariateAddSub_eval, bivariateRight_eval]
    simp only [Polynomial.eval_add]
    rw [Polynomial.evalEval_zero] at hderxy
    linear_combination -(hderxy + hcderxy)
  let c : k := (C.coeff 1 + f.derivative).eval 0
  have hconst : C.coeff 1 + f.derivative = Polynomial.C c := by
    apply Polynomial.funext
    intro x
    have hx := congrArg (fun Q : BivariatePolynomial k => Q.evalEval x 0) hzero
    rw [bivariateAddSub_eval, bivariateRight_eval] at hx
    simpa [c] using hx
  have hbad : ∀ n : ℕ, (n + 1 : k) = 0 → (C.coeff 1).coeff n = 0 := by
    intro n hn
    have hn0 : n ≠ 0 := by
      intro hn0
      subst n
      exact one_ne_zero (by simpa only [Nat.cast_zero, zero_add] using hn)
    have hcoeff := congrArg (fun q : Polynomial k => q.coeff n) hconst
    have hfd : f.derivative.coeff n = 0 := by
      rw [Polynomial.coeff_derivative]
      rw [hn]
      simp
    have hcc : (Polynomial.C c).coeff n = 0 := by
      rw [Polynomial.coeff_C]
      simp [hn0]
    have hcoeff' : (C.coeff 1).coeff n + f.derivative.coeff n =
        (Polynomial.C c).coeff n := by
      simpa [Polynomial.coeff_add] using hcoeff
    rw [hfd, hcc] at hcoeff'
    simpa using hcoeff'
  let h : Polynomial k := formalIntegral (C.coeff 1)
  have hh : h.derivative = C.coeff 1 :=
    derivative_formalIntegral hbad
  refine ⟨h, rfl, ?_⟩
  rw [hcder, additiveCoboundary_derivative, hh]

private lemma bivariateAddSub_natDegree_le (f : Polynomial k) :
    (bivariateAddSub f).natDegree ≤ f.natDegree := by
  rw [bivariateAddSub, Polynomial.eval₂_eq_sum_range]
  apply Polynomial.natDegree_sum_le_of_forall_le _ _ (n := f.natDegree)
  intro i hi
  have hi' : i ≤ f.natDegree := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hu : (((Polynomial.C (R := Polynomial k) Polynomial.X) +
      (Polynomial.X : BivariatePolynomial k)).natDegree) ≤ 1 := by
    exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
      (by simp [Polynomial.natDegree_X]))
  calc
    (Polynomial.C (Polynomial.C (f.coeff i)) *
        ((Polynomial.C (R := Polynomial k) Polynomial.X) +
          (Polynomial.X : BivariatePolynomial k)) ^ i).natDegree ≤
        (Polynomial.C (Polynomial.C (f.coeff i))).natDegree +
          ((((Polynomial.C (R := Polynomial k) Polynomial.X) +
            (Polynomial.X : BivariatePolynomial k)) ^ i).natDegree) :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + i := by
      simp only [Polynomial.natDegree_C]
      simpa only [Nat.mul_one, zero_add] using
        (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left i hu))
    _ ≤ f.natDegree := by simpa using hi'

private lemma bivariateRight_natDegree_le (f : Polynomial k) :
    (bivariateRight f).natDegree ≤ f.natDegree := by
  rw [bivariateRight]
  exact Polynomial.natDegree_map_le

private lemma additiveCoboundary_natDegree_le (f : Polynomial k) :
    (additiveCoboundary f).natDegree ≤ f.natDegree := by
  rw [additiveCoboundary]
  calc
    (bivariateAddSub f - bivariateLeft f - bivariateRight f).natDegree ≤
        max (bivariateAddSub f - bivariateLeft f).natDegree
          (bivariateRight f).natDegree := Polynomial.natDegree_sub_le _ _
    _ ≤ f.natDegree := max_le
      ((Polynomial.natDegree_sub_le _ _).trans (max_le
        (bivariateAddSub_natDegree_le f) (by simp [bivariateLeft])))
      (bivariateRight_natDegree_le f)

private lemma bivariateAddSub_coeff_natDegree (h : Polynomial k) :
    (bivariateAddSub h).coeff h.natDegree = Polynomial.C h.leadingCoeff := by
  let q : BivariatePolynomial k :=
    (Polynomial.C (R := Polynomial k) Polynomial.X) +
      (Polynomial.X : BivariatePolynomial k)
  have hqmonic : q.Monic := by
    dsimp [q]
    simpa only [add_comm] using (Polynomial.monic_X_add_C (Polynomial.X : Polynomial k))
  have hqdeg : q.natDegree = 1 := by
    dsimp [q]
    simpa only [add_comm] using (Polynomial.natDegree_X_add_C (Polynomial.X : Polynomial k))
  have hqpowcoef (i : ℕ) (hi_le : i ≤ h.natDegree) :
      (q ^ i).coeff h.natDegree = if i = h.natDegree then 1 else 0 := by
    by_cases hieq : i = h.natDegree
    · subst i
      have hpmonic : (q ^ h.natDegree).Monic := hqmonic.pow _
      have hpdeg : (q ^ h.natDegree).natDegree = h.natDegree := by
        rw [hqmonic.natDegree_pow, hqdeg]
        simp
      simpa [hpdeg] using hpmonic.coeff_natDegree
    · have hilt : i < h.natDegree := Nat.lt_of_le_of_ne hi_le hieq
      have hpowdeg : (q ^ i).natDegree = i := by
        rw [hqmonic.natDegree_pow, hqdeg]
        simp
      have hltdeg : (q ^ i).natDegree < h.natDegree := by
        simpa [hpowdeg] using hilt
      simpa [hieq] using (Polynomial.coeff_eq_zero_of_natDegree_lt hltdeg)
  rw [bivariateAddSub, Polynomial.eval₂_eq_sum_range,
    Polynomial.finsetSum_coeff]
  have hterm (i : ℕ) (hi : i ∈ Finset.range (h.natDegree + 1)) :
      (((Polynomial.C : Polynomial k →+* BivariatePolynomial k).comp
          (Polynomial.C : k →+* Polynomial k)) (h.coeff i) * q ^ i).coeff h.natDegree =
        if i = h.natDegree then Polynomial.C (h.coeff i) else 0 := by
    rw [show ((Polynomial.C : Polynomial k →+* BivariatePolynomial k).comp
      (Polynomial.C : k →+* Polynomial k)) (h.coeff i) =
      Polynomial.C (Polynomial.C (h.coeff i)) by rfl]
    have hi_le : i ≤ h.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    rw [Polynomial.coeff_C_mul, hqpowcoef i hi_le]
    split_ifs <;> simp_all
  have hsumterm :
      (∑ i ∈ Finset.range (h.natDegree + 1),
        (((Polynomial.C : Polynomial k →+* BivariatePolynomial k).comp
            (Polynomial.C : k →+* Polynomial k)) (h.coeff i) * q ^ i).coeff h.natDegree) =
      ∑ i ∈ Finset.range (h.natDegree + 1),
        (if i = h.natDegree then Polynomial.C (h.coeff i) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm i hi
  rw [hsumterm]
  have hsum := Finset.sum_eq_single h.natDegree
    (s := Finset.range (h.natDegree + 1))
    (f := fun i => if i = h.natDegree then Polynomial.C (h.coeff i) else 0)
    (by intro b hb hbn; simp [hbn])
    (by intro hmem; exact (hmem (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim)
  rw [hsum]
  simp only [ite_true, Polynomial.coeff_natDegree]

private lemma bivariateRight_coeff_natDegree (h : Polynomial k) :
    (bivariateRight h).coeff h.natDegree = Polynomial.C h.leadingCoeff := by
  simp only [bivariateRight, Polynomial.coeff_map]
  rw [Polynomial.coeff_natDegree]

private lemma additiveCoboundary_coeff_natDegree (h : Polynomial k)
    (hpos : 0 < h.natDegree) :
    (additiveCoboundary h).coeff h.natDegree = 0 := by
  rw [additiveCoboundary, Polynomial.coeff_sub, Polynomial.coeff_sub]
  rw [bivariateAddSub_coeff_natDegree h]
  have hleft : (bivariateLeft h).coeff h.natDegree = 0 := by
    simp [bivariateLeft, Polynomial.coeff_C, hpos.ne']
  have hright : (bivariateRight h).coeff h.natDegree =
      Polynomial.C h.leadingCoeff := bivariateRight_coeff_natDegree h
  rw [hleft, hright]
  simp

private lemma additiveCoboundary_natDegree_lt (h : Polynomial k)
    (hpos : 0 < h.natDegree) :
    (additiveCoboundary h).natDegree < h.natDegree := by
  by_cases hz : additiveCoboundary h = 0
  · rw [hz]
    exact hpos
  have hle : (additiveCoboundary h).natDegree ≤ h.natDegree :=
    additiveCoboundary_natDegree_le h
  by_contra hnot
  have heq : (additiveCoboundary h).natDegree = h.natDegree :=
    Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
  have hcoeff : (additiveCoboundary h).coeff h.natDegree ≠ 0 := by
    rw [← heq]
    exact Polynomial.leadingCoeff_ne_zero.mpr hz
  exact hcoeff (additiveCoboundary_coeff_natDegree h hpos)

private lemma coeff_swap (C : BivariatePolynomial k) (i j : ℕ) :
    ((Polynomial.Bivariate.swap C).coeff i).coeff j = (C.coeff j).coeff i := by
  induction C using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [map_add, Polynomial.coeff_add]
      rw [hP, hQ]
  | monomial n a =>
      induction a using Polynomial.induction_on' with
      | add P Q hP hQ =>
          have hmon : Polynomial.monomial n (P + Q) =
              Polynomial.monomial n P + Polynomial.monomial n Q := by
            apply Polynomial.ext
            intro i
            simp only [Polynomial.coeff_monomial, Polynomial.coeff_add]
            split_ifs <;> simp_all
          rw [hmon, map_add]
          simp only [Polynomial.coeff_add]
          rw [hP, hQ]
      | monomial m b =>
          rw [Polynomial.Bivariate.swap_monomial_monomial]
          simp only [Polynomial.coeff_monomial]
          by_cases h₁ : m = i <;> by_cases h₂ : n = j <;>
            simp [Polynomial.coeff_monomial, h₁, h₂]

private lemma coeff_natDegree_le_of_swap_eq {C : BivariatePolynomial k}
    (hswap : Polynomial.Bivariate.swap C = C) (j : ℕ) :
    (C.coeff j).natDegree ≤ C.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hC : C.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hn
  have hs := congrArg (fun Q : BivariatePolynomial k => Q.coeff n) hswap
  have hs' := congrArg (fun Q : Polynomial k => Q.coeff j) hs
  rw [coeff_swap] at hs'
  rw [hC] at hs'
  simpa using hs'

private lemma evalEval_right_zero (C : BivariatePolynomial k) (x : k) :
    C.evalEval x 0 = (C.coeff 0).eval x := by
  induction C using Polynomial.induction_on with
  | C a => simp [Polynomial.evalEval]
  | add p q hp hq =>
      simp only [Polynomial.evalEval_add, Polynomial.coeff_add,
        Polynomial.eval_add, hp, hq]
  | monomial n a hn =>
      simp [Polynomial.evalEval]

private lemma normalized_outer_degree_zero
    [IsAlgClosed k] {C : BivariatePolynomial k}
    (hnorm : IsNormalizedPolynomialCocycle C)
    (hdeg : C.natDegree ≤ 0) : C = 0 := by
  have hCconst : C = Polynomial.C (C.coeff 0) :=
    Polynomial.eq_C_of_natDegree_le_zero hdeg
  have hcoeff0 : C.coeff 0 = 0 := by
    apply Polynomial.funext
    intro y
    have hy := (isNormalizedPolynomialCocycle_iff C).mp hnorm |>.2 y
    rw [hCconst] at hy
    simpa [Polynomial.evalEval, Polynomial.coeff_zero_eq_eval_zero] using hy
  rw [hCconst, hcoeff0]
  simp

private lemma bivariate_swap_eq [Infinite k] {C : BivariatePolynomial k}
    (hs : IsSymmetricPolynomialCocycle C) : Polynomial.Bivariate.swap C = C := by
  apply Polynomial.ext
  intro i
  apply Polynomial.funext
  intro x
  have hp :
      (Polynomial.Bivariate.swap C).map (Polynomial.evalRingHom x) =
        C.map (Polynomial.evalRingHom x) := by
    apply Polynomial.funext
    intro y
    rw [Polynomial.map_evalRingHom_eval, Polynomial.map_evalRingHom_eval]
    have hswapEval := Polynomial.Bivariate.aevalAeval_swap x y C
    have hswapEval' :
        (Polynomial.Bivariate.swap C).evalEval x y = C.evalEval y x := by
      simpa only [Polynomial.coe_aevalAeval_eq_evalEval] using hswapEval
    calc
      (Polynomial.Bivariate.swap C).evalEval x y = C.evalEval y x := hswapEval'
      _ = C.evalEval x y := (isSymmetricPolynomialCocycle_iff C).mp hs y x
  have hi := congrArg (fun q : Polynomial k => q.coeff i) hp
  simpa [Polynomial.coeff_map] using hi

private lemma inner_derivative_zero_of_symmetric_outer_derivative_zero
    [Infinite k] {C : BivariatePolynomial k}
    (hs : IsSymmetricPolynomialCocycle C) (hder : C.derivative = 0) :
    ∀ j, (C.coeff j).derivative = 0 := by
  have hswap := bivariate_swap_eq hs
  have hsder : (Polynomial.Bivariate.swap C).derivative = 0 := by
    rw [hswap, hder]
  intro j
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_derivative]
  have hi := congrArg (fun q : BivariatePolynomial k => q.coeff i) hsder
  have hij := congrArg (fun q : Polynomial k => q.coeff j) hi
  rw [Polynomial.coeff_derivative] at hij
  have hscalar : (↑i + 1 : Polynomial k) = Polynomial.C (↑i + 1 : k) := by
    calc
      (↑i + 1 : Polynomial k) = Polynomial.C (↑i : k) + Polynomial.C (1 : k) := by
        simp
      _ = Polynomial.C ((↑i : k) + 1) := by rw [← Polynomial.C_add]
  rw [hscalar, Polynomial.coeff_mul_C] at hij
  rw [coeff_swap] at hij
  simpa [Polynomial.coeff_derivative] using hij

private lemma polynomial_coboundary_core
    {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    {C : BivariatePolynomial k} {f : Polynomial k}
    (hnorm : IsNormalizedPolynomialCocycle C)
    (hsym : IsSymmetricPolynomialCocycle C)
    (hcoc : IsAdditivePolynomialTwoCocycle C)
    (hartin : C ^ p - C = additiveCoboundary f) :
    ∃ h : Polynomial k, C = additiveCoboundary h := by
  induction hn : C.natDegree using Nat.strong_induction_on generalizing C f with
  | h n ih =>
      by_cases hn0 : n = 0
      · have hzero : C = 0 :=
          normalized_outer_degree_zero hnorm (by omega)
        refine ⟨0, ?_⟩
        rw [hzero, additiveCoboundary_zero]
      have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      obtain ⟨h0, hh0, hder⟩ := derivative_reduction hcoc hartin
      have h0eval : h0.eval 0 = 0 := by
        rw [hh0]
        exact formalIntegral_eval_zero _
      let R : BivariatePolynomial k := C - additiveCoboundary h0
      have hRder : R.derivative = 0 := by
        dsimp [R]
        rw [Polynomial.derivative_sub, hder]
        ring
      have hRnorm : IsNormalizedPolynomialCocycle R :=
        normalized_sub hnorm (additiveCoboundary_normalized h0 h0eval)
      have hRsym : IsSymmetricPolynomialCocycle R :=
        symmetric_sub hsym (additiveCoboundary_symmetric h0)
      have hRcoc : IsAdditivePolynomialTwoCocycle R :=
        cocycle_sub hcoc (additiveCoboundary_cocycle h0)
      have hswap : Polynomial.Bivariate.swap C = C := bivariate_swap_eq hsym
      have hcoeffdeg : (C.coeff 1).natDegree ≤ C.natDegree :=
        coeff_natDegree_le_of_swap_eq hswap 1
      have h0deg : h0.natDegree ≤ n + 1 := by
        rw [hh0]
        exact (formalIntegral_natDegree_le (C.coeff 1)).trans
          (Nat.add_le_add_right (hcoeffdeg.trans_eq hn) 1)
      have hdelta_deg : (additiveCoboundary h0).natDegree ≤ n := by
        by_cases h0pos : 0 < h0.natDegree
        · have hlt := additiveCoboundary_natDegree_lt h0 h0pos
          omega
        · have hle := additiveCoboundary_natDegree_le h0
          omega
      have hRdeg : R.natDegree ≤ n := by
        dsimp [R]
        exact (Polynomial.natDegree_sub_le _ _).trans
          (max_le hn.le hdelta_deg)
      have hinner : ∀ j, (R.coeff j).derivative = 0 :=
        inner_derivative_zero_of_symmetric_outer_derivative_zero hRsym hRder
      obtain ⟨E, hpow⟩ := exists_bivariate_pth_root hRder hinner
      have hEnorm : IsNormalizedPolynomialCocycle E := pth_root_normalized hpow hRnorm
      have hEsym : IsSymmetricPolynomialCocycle E := pth_root_symmetric hpow hRsym
      have hEcoc : IsAdditivePolynomialTwoCocycle E := pth_root_cocycle hpow hRcoc
      have hDpow : (E ^ p - E) ^ p =
          additiveCoboundary (f - (h0 ^ p - h0)) := by
        rw [sub_pow_char, hpow]
        dsimp [R]
        rw [sub_pow_char, additiveCoboundary_sub, additiveCoboundary_sub,
          additiveCoboundary_pow, ← hartin]
        ring
      obtain ⟨g, hg⟩ := additiveCoboundary_derivative_zero_root hDpow
      have hElt : E.natDegree < n := by
        have hElt' := pth_root_natDegree_lt hpow hRdeg hnpos
        omega
      obtain ⟨q, hq⟩ := ih E.natDegree hElt hEnorm hEsym hEcoc hg rfl
      have hEq : C = additiveCoboundary h0 + E ^ p := by
        dsimp [R] at hpow
        linear_combination -hpow
      have hqpow : E ^ p = additiveCoboundary (q ^ p) := by
        rw [hq]
        exact (additiveCoboundary_pow q).symm
      refine ⟨h0 + q ^ p, ?_⟩
      rw [additiveCoboundary_add, ← hqpow]
      exact hEq

/-- Straighten a polynomial Artin--Schreier cocycle without an a priori
cohomology certificate.  The proof differentiates the cocycle identity to
construct a low-degree primitive, subtracts it, and takes coefficientwise
Frobenius roots; symmetry supplies the second zero-derivative condition, and
the residual Artin--Schreier equation is handled recursively by strong
induction on outer degree. -/
public theorem polynomial_artin_schreier_cocycle_straightening
    {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    {C : BivariatePolynomial k} {f : Polynomial k}
    (hnormalized : IsNormalizedPolynomialCocycle C)
    (hsymmetric : IsSymmetricPolynomialCocycle C)
    (hcocycle : IsAdditivePolynomialTwoCocycle C)
    (hartin : C ^ p - C = additiveCoboundary f) :
    ∃ h P : Polynomial k,
      C = additiveCoboundary h ∧
      P = f - (h ^ p - h) ∧
      IsAdditivePolynomial P := by
  obtain ⟨h, hCh⟩ := polynomial_coboundary_core
    hnormalized hsymmetric hcocycle hartin
  refine ⟨h, f - (h ^ p - h), hCh, rfl, ?_⟩
  exact additiveCoboundary_straightened_is_additive hCh hartin

private lemma additive_zero (k : Type u) [Field k] :
    IsAdditivePolynomial (0 : Polynomial k) := by
  rw [isAdditivePolynomial_iff]
  intro x y
  simp

private lemma additive_add {f g : Polynomial k}
    (hf : IsAdditivePolynomial f) (hg : IsAdditivePolynomial g) :
    IsAdditivePolynomial (f + g) := by
  rw [isAdditivePolynomial_iff]
  intro x y
  simp only [Polynomial.eval_add, (isAdditivePolynomial_iff f).mp hf x y,
    (isAdditivePolynomial_iff g).mp hg x y]
  abel

private lemma additive_sub {f g : Polynomial k}
    (hf : IsAdditivePolynomial f) (hg : IsAdditivePolynomial g) :
    IsAdditivePolynomial (f - g) := by
  rw [isAdditivePolynomial_iff]
  intro x y
  simp only [Polynomial.eval_sub, (isAdditivePolynomial_iff f).mp hf x y,
    (isAdditivePolynomial_iff g).mp hg x y]
  abel

private lemma additive_C_mul (a : k) {f : Polynomial k}
    (hf : IsAdditivePolynomial f) :
    IsAdditivePolynomial (Polynomial.C a * f) := by
  rw [isAdditivePolynomial_iff]
  intro x y
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    (isAdditivePolynomial_iff f).mp hf x y]
  rw [mul_add]

private lemma additive_pow_char
    {p : ℕ} [Fact p.Prime] [CharP k p]
    {f : Polynomial k} (hf : IsAdditivePolynomial f) :
    IsAdditivePolynomial (f ^ p) := by
  rw [isAdditivePolynomial_iff]
  intro x y
  have hxy := (isAdditivePolynomial_iff f).mp hf x y
  simp only [Polynomial.eval_pow]
  rw [hxy]
  simpa only [pow_one] using add_pow_char_pow (f.eval x) (f.eval y) p 1

private lemma additive_artinSchreier
    {p : ℕ} [Fact p.Prime] [CharP k p]
    {f : Polynomial k} (hf : IsAdditivePolynomial f) :
    IsAdditivePolynomial (f ^ p - f) :=
  additive_sub (additive_pow_char hf) hf

private lemma top_artinSchreier_reduction
    {p m : ℕ} [Fact p.Prime] [CharP k p]
    {P : Polynomial k} (hPne : P ≠ 0)
    (hPm : P.natDegree = p ^ m) (hm : 0 < m)
    {b : k} (hb : b ^ p = P.leadingCoeff) :
    let e := p ^ (m - 1)
    let h := Polynomial.C b * Polynomial.X ^ e
    (P - (h ^ p - h)).natDegree < P.natDegree := by
  dsimp
  let e := p ^ (m - 1)
  let h : Polynomial k := Polynomial.C b * Polynomial.X ^ e
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
  have hpe : e * p = p ^ m := by
    dsimp [e]
    calc
      p ^ (m - 1) * p = p ^ ((m - 1) + 1) := (pow_succ p (m - 1)).symm
      _ = p ^ m := by rw [hm1]
  have hhpow : h ^ p = Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree := by
    dsimp [h]
    rw [mul_pow, ← Polynomial.C_pow, ← pow_mul, hb, hpe, hPm]
  rw [show P - (h ^ p - h) = P - h ^ p + h by ring, hhpow,
    Polynomial.self_sub_C_mul_X_pow]
  have he_lt : e < P.natDegree := by
    rw [hPm, ← hpe]
    simpa using ((Nat.mul_lt_mul_left (pow_pos (Fact.out : p.Prime).pos _)).mpr
      (Fact.out : p.Prime).one_lt)
  calc
    (P.eraseLead + h).natDegree ≤
        max P.eraseLead.natDegree h.natDegree := Polynomial.natDegree_add_le _ _
    _ < P.natDegree := max_lt
      (lt_of_le_of_lt (Polynomial.eraseLead_natDegree_le P) (by omega))
      (by
        have hbne : b ≠ 0 := by
          intro hb0
          rw [hb0, zero_pow (Fact.out : p.Prime).ne_zero] at hb
          exact Polynomial.leadingCoeff_ne_zero.mpr hPne hb.symm
        have hnat : h.natDegree = e := by
          rw [Polynomial.natDegree_C_mul hbne, Polynomial.natDegree_pow,
            Polynomial.natDegree_X, Nat.mul_one]
        exact hnat ▸ he_lt)

/-- Every additive polynomial is congruent modulo an Artin--Schreier
polynomial `h^p-h` to a linear polynomial `aX`, with `h` itself additive. -/
public theorem additivePolynomial_congruent_linear_with_additive_correction
    {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (P : Polynomial k) (hP : IsAdditivePolynomial P) :
    ∃ h : Polynomial k, ∃ a : k,
      IsAdditivePolynomial h ∧
      P - (h ^ p - h) = Polynomial.C a * Polynomial.X := by
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | h n ih =>
      by_cases hPzero : P = 0
      · refine ⟨0, 0, additive_zero k, ?_⟩
        simp [hPzero, (Fact.out : p.Prime).ne_zero]
      obtain ⟨m, hm⟩ := additivePolynomial_natDegree_eq_ringChar_pow hP hPzero
      rw [ringChar.eq k p] at hm
      by_cases hm0 : m = 0
      · have hdegree : P.natDegree = 1 := by simpa [hm0] using hm
        have hconst : P.coeff 0 = 0 := by
          rw [Polynomial.coeff_zero_eq_eval_zero]
          have h := ((isAdditivePolynomial_iff P).mp hP) 0 0
          simpa using h
        have hlinear : P = Polynomial.C (P.coeff 1) * Polynomial.X := by
          simpa [hconst] using
            (Polynomial.eq_X_add_C_of_natDegree_le_one (p := P) hdegree.le)
        refine ⟨0, P.coeff 1, additive_zero k, ?_⟩
        rw [hlinear]
        simp only [zero_pow (Fact.out : p.Prime).ne_zero, sub_zero]
        simp
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        obtain ⟨b, hb⟩ :=
          IsAlgClosed.exists_pow_nat_eq P.leadingCoeff (Fact.out : p.Prime).pos
        let e := p ^ (m - 1)
        let h0 : Polynomial k := Polynomial.C b * Polynomial.X ^ e
        let Q : Polynomial k := P - (h0 ^ p - h0)
        have hh0 : IsAdditivePolynomial h0 := by
          exact additive_C_mul b (pPower_isAdditive p (m - 1))
        have hQ : IsAdditivePolynomial Q := by
          exact additive_sub hP (additive_artinSchreier hh0)
        have hQdegree : Q.natDegree < P.natDegree := by
          change (P - (h0 ^ p - h0)).natDegree < P.natDegree
          simpa only [h0, e] using
            top_artinSchreier_reduction hPzero hm hmpos hb
        have hQlt : Q.natDegree < n := by
          rw [← hn]
          exact hQdegree
        obtain ⟨h1, a, hh1, hQa⟩ := ih Q.natDegree hQlt Q hQ rfl
        refine ⟨h0 + h1, a, additive_add hh0 hh1, ?_⟩
        have haddpow : (h0 + h1) ^ p = h0 ^ p + h1 ^ p := by
          simpa only [pow_one] using add_pow_char_pow h0 h1 p 1
        dsimp [Q] at hQa
        rw [haddpow]
        rw [← hQa]
        ring

/-- Every additive polynomial is congruent modulo an Artin--Schreier
polynomial `h^p-h` to a linear polynomial `aX`. -/
public theorem additivePolynomial_congruent_linear
    {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k]
    (P : Polynomial k) (hP : IsAdditivePolynomial P) :
    ∃ h : Polynomial k, ∃ a : k,
      P - (h ^ p - h) = Polynomial.C a * Polynomial.X := by
  obtain ⟨h, a, _, hlinear⟩ :=
    additivePolynomial_congruent_linear_with_additive_correction P hP
  exact ⟨h, a, hlinear⟩

end
end Theory.AlgebraicGroup

module

public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.FieldTheory.RatFunc.Luroth
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Automorphisms of a rational function field are Mobius transformations

Every algebra automorphism of `k(X)` sends `X` to a fractional linear
expression with coefficients forming an invertible two-by-two matrix.  This is
the algebraic form of the standard identification of `Aut_k(k(X))` with
`PGL₂(k)`.  The result is kept at the field-theory layer for use in pole-support
arguments, in particular the rational-curve step of Borel, *Linear Algebraic
Groups*, Theorem 10.9 (`refs/KGroup/Bor1/Chapter3.tex`).

For an automorphism `sigma`, transport of `k⟮X⟯ = k⟮X⟯` along `sigma` shows
that `sigma X` still generates the whole rational function field.  Hence the
relative finrank of `k(X)` over `k(sigma X)` is one.  Mathlib's
`RatFunc.finrank_eq_max_natDegree` identifies this finrank with the maximum of
the degrees of the normalized numerator and denominator, so both are linear.
If the resulting coefficient determinant vanished, the two linear
polynomials would be proportional and `sigma X` would be constant, contrary
to the same degree computation.  The coefficients therefore define an element
of `GL (Fin 2) k` via `Matrix.GeneralLinearGroup.mkOfDetNeZero`.

The module also records two consequences used by clients.  Applying an
automorphism is substitution of its value on `X` into the normalized numerator
and denominator, and consequently two rational-function automorphisms that
agree on `X` are equal.  All degree and coefficient calculations remain
private; only these stable interfaces and the Mobius classification are public.
-/

universe u

open IntermediateField Polynomial

namespace RatFunc

variable {k : Type u} [Field k]

/-- Applying a rational-function automorphism is substitution of its image of
`X` into the normalized numerator and denominator. -/
public theorem algEquiv_apply_eq_aeval_num_div_denom
    (sigma : RatFunc k ≃ₐ[k] RatFunc k) (f : RatFunc k) :
    sigma f =
      Polynomial.aeval (sigma (X : RatFunc k)) f.num /
        Polynomial.aeval (sigma (X : RatFunc k)) f.denom := by
  calc
    sigma f = sigma (algebraMap k[X] (RatFunc k) f.num /
        algebraMap k[X] (RatFunc k) f.denom) :=
      congrArg sigma (num_div_denom f).symm
    _ = sigma (Polynomial.aeval (X : RatFunc k) f.num) /
        sigma (Polynomial.aeval (X : RatFunc k) f.denom) := by
      rw [map_div₀, aeval_X_left_eq_algebraMap, aeval_X_left_eq_algebraMap]
    _ = Polynomial.aeval (sigma (X : RatFunc k)) f.num /
        Polynomial.aeval (sigma (X : RatFunc k)) f.denom := by
      rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_algHom_apply]

/-- Two `k`-algebra automorphisms of `k(X)` are equal when they agree on `X`. -/
public theorem algEquiv_ext_X {sigma tau : RatFunc k ≃ₐ[k] RatFunc k}
    (h : sigma (X : RatFunc k) = tau (X : RatFunc k)) : sigma = tau := by
  apply DFunLike.ext sigma tau
  intro f
  calc
    sigma f = Polynomial.aeval (sigma (X : RatFunc k)) f.num /
        Polynomial.aeval (sigma (X : RatFunc k)) f.denom :=
      algEquiv_apply_eq_aeval_num_div_denom sigma f
    _ = Polynomial.aeval (tau (X : RatFunc k)) f.num /
        Polynomial.aeval (tau (X : RatFunc k)) f.denom := by rw [h]
    _ = tau f := (algEquiv_apply_eq_aeval_num_div_denom tau f).symm

private lemma algEquiv_adjoin_X_eq_top (sigma : RatFunc k ≃ₐ[k] RatFunc k) :
    IntermediateField.adjoin k {sigma (X : RatFunc k)} = ⊤ := by
  change IntermediateField.adjoin k {sigma.toAlgHom (X : RatFunc k)} = ⊤
  calc
    IntermediateField.adjoin k {sigma.toAlgHom (X : RatFunc k)} =
        (IntermediateField.adjoin k {(X : RatFunc k)}).map sigma.toAlgHom := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]
    _ = (⊤ : IntermediateField k (RatFunc k)).map sigma.toAlgHom := by
      rw [RatFunc.adjoin_X]
    _ = sigma.toAlgHom.fieldRange :=
      (AlgHom.fieldRange_eq_map sigma.toAlgHom).symm
    _ = ⊤ := sigma.fieldRange_eq_top

private lemma algEquiv_X_max_natDegree (sigma : RatFunc k ≃ₐ[k] RatFunc k) :
    max (sigma (X : RatFunc k)).num.natDegree
      (sigma (X : RatFunc k)).denom.natDegree = 1 := by
  rw [← RatFunc.finrank_eq_max_natDegree]
  rw [algEquiv_adjoin_X_eq_top sigma]
  exact IntermediateField.finrank_top

private lemma exists_mobius_coefficients (sigma : RatFunc k ≃ₐ[k] RatFunc k) :
    ∃ a b c d : k,
      a * d - b * c ≠ 0 ∧
      sigma (X : RatFunc k) =
        (C a * X + C b) / (C c * X + C d) := by
  let y := sigma (X : RatFunc k)
  have hdegree := algEquiv_X_max_natDegree sigma
  have hnum : y.num.natDegree ≤ 1 :=
    (le_max_left y.num.natDegree y.denom.natDegree).trans_eq hdegree
  have hdenom : y.denom.natDegree ≤ 1 :=
    (le_max_right y.num.natDegree y.denom.natDegree).trans_eq hdegree
  let a := y.num.coeff 1
  let b := y.num.coeff 0
  let c := y.denom.coeff 1
  let d := y.denom.coeff 0
  have hp : y.num = Polynomial.C a * Polynomial.X + Polynomial.C b :=
    y.num.eq_X_add_C_of_natDegree_le_one hnum
  have hq : y.denom = Polynomial.C c * Polynomial.X + Polynomial.C d :=
    y.denom.eq_X_add_C_of_natDegree_le_one hdenom
  have hy : y = (C a * X + C b) / (C c * X + C d) := by
    calc
      y = algebraMap k[X] (RatFunc k) y.num /
          algebraMap k[X] (RatFunc k) y.denom := (num_div_denom y).symm
      _ = (C a * X + C b) / (C c * X + C d) := by rw [hp, hq]; simp
  refine ⟨a, b, c, d, ?_, by simpa [y] using hy⟩
  intro hdet
  have hyC : ∃ z : k, y = C z := by
    by_cases hc : c = 0
    · have hd : d ≠ 0 := by
        intro hd
        apply y.denom_ne_zero
        simp [hq, hc, hd]
      have ha : a = 0 := by
        have : a * d = 0 := by simpa [hc] using hdet
        exact (mul_eq_zero.mp this).resolve_right hd
      refine ⟨b / d, ?_⟩
      rw [hy, hc, ha]
      simp
    · have hb : b = (a / c) * d := by
        apply (mul_right_cancel₀ hc)
        calc
          b * c = a * d := (sub_eq_zero.mp hdet).symm
          _ = (a / c * d) * c := by field_simp [hc]
      refine ⟨a / c, ?_⟩
      rw [hy, hb]
      have hden : C c * (X : RatFunc k) + C d ≠ 0 := by
        simpa [hq] using (algebraMap_ne_zero y.denom_ne_zero :
          algebraMap k[X] (RatFunc k) y.denom ≠ 0)
      apply (div_eq_iff hden).2
      simp only [map_mul, map_div₀]
      field_simp [hc]
  have hconstant : y.num.natDegree = 0 ∧ y.denom.natDegree = 0 :=
    (y.eq_C_iff).mp hyC
  rw [hconstant.1, hconstant.2] at hdegree
  simp at hdegree

/-- Every `k`-algebra automorphism of `k(X)` sends `X` by an invertible
two-by-two fractional linear transformation. -/
public theorem algEquiv_X_eq_mobius (sigma : RatFunc k ≃ₐ[k] RatFunc k) :
    ∃ g : GL (Fin 2) k,
      sigma (X : RatFunc k) =
        (C (g 0 0) * X + C (g 0 1)) /
          (C (g 1 0) * X + C (g 1 1)) := by
  obtain ⟨a, b, c, d, hdet, hsigma⟩ := exists_mobius_coefficients sigma
  let A : Matrix (Fin 2) (Fin 2) k := !![a, b; c, d]
  have hA : Matrix.det A ≠ 0 := by
    simpa [A, Matrix.det_fin_two] using hdet
  let g : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA
  refine ⟨g, ?_⟩
  simpa [g, A] using hsigma

end RatFunc

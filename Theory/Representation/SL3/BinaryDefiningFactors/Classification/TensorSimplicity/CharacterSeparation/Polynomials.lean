/-
The multiplication-degree proof is adapted from Mathlib:
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the adapted proof: Antoine Chambert-Loir, Bolton Bailey
-/
module
public import Theory.Representation.SL3.BinaryDefiningFactors
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.RestrictedSeparation
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FinCases

/-!
# Polynomial separation of binary SL₃ words

The four factor polynomials are `1`, `X`, `Y` and `1 + X * Y`. A word has
polynomial equal to its head polynomial times the square of its tail polynomial.
The two individual degrees are the binary integers whose digit pairs encode its
letters. They are strictly below `2 ^ length`, and their parities successively
recover every letter of a word of fixed length.

Interpolation on the whole finite-field grid is proved by induction on the
number of variables, applying the univariate root bound to each specialization.
In particular, evaluation retains the distinction between degrees zero and
`|F| - 1`, including when `|F| = 2`.

Source: the uniqueness assertion in GLS III, 2.8.6(a), specialized to the four
factors in 2.8.10(c). The private multiplication-degree proof is adapted from
Mathlib.Algebra.MvPolynomial.NoZeroDivisors.degreeOf_mul_eq, using only its
polynomial-equivalence dependencies.
-/

public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Representation.SL3.BinaryDefiningFactors.TensorSimplicity.CharacterSeparation
open MvPolynomial
variable (F : Type*) [Field F]

private lemma degreeOf_mul' {σ : Type*} (i : σ) {p q : MvPolynomial σ F}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    degreeOf i (p * q) = degreeOf i p + degreeOf i q := by
  classical
  simp_rw [degreeOf_eq_natDegree, map_mul, ← renameEquiv_apply]
  rw [Polynomial.natDegree_mul] <;>
    simpa [-renameEquiv_apply, EmbeddingLike.map_eq_zero_iff]

private lemma degreeOf_sq (i : Fin 2) (p : MvPolynomial (Fin 2) F) (hp : p ≠ 0) :
    degreeOf i (p ^ 2) = 2 * degreeOf i p := by
  rw [pow_two, degreeOf_mul' F i hp hp]
  omega

/-- The restricted-factor polynomials, with variables for trace and inverse trace. -/
@[expose] def factorPolynomial : Factor → MvPolynomial (Fin 2) F
  | .trivial => 1
  | .natural => X 0
  | .dual => X 1
  | .adjoint => 1 + X 0 * X 1

/-- The character polynomial of a word, with each successive factor squared. -/
@[expose] def wordPolynomial : List Factor → MvPolynomial (Fin 2) F
  | [] => 1
  | a :: w => factorPolynomial F a * wordPolynomial w ^ 2

private def factorDigit : Factor → Fin 2 → ℕ
  | .trivial => ![0, 0]
  | .natural => ![1, 0]
  | .dual => ![0, 1]
  | .adjoint => ![1, 1]

private def wordWeight : List Factor → Fin 2 → ℕ
  | [] => fun _ => 0
  | a :: w => fun i => factorDigit a i + 2 * wordWeight w i

private lemma factorDigit_le_one (a : Factor) (i : Fin 2) : factorDigit a i ≤ 1 := by
  cases a <;> fin_cases i <;> simp [factorDigit]

private lemma degreeOf_factorPolynomial (a : Factor) (i : Fin 2) :
    (factorPolynomial F a).degreeOf i = factorDigit a i := by
  have hprod : (X 0 * X 1 : MvPolynomial (Fin 2) F).degreeOf i = 1 := by
    rw [degreeOf_mul' F i (X_ne_zero 0) (X_ne_zero 1)]
    fin_cases i <;> simp [degreeOf_X]
  cases a with
  | trivial => fin_cases i <;> simp [factorPolynomial, factorDigit]
  | natural => fin_cases i <;> simp [factorPolynomial, factorDigit, degreeOf_X]
  | dual => fin_cases i <;> simp [factorPolynomial, factorDigit, degreeOf_X]
  | adjoint =>
    have h := degreeOf_add_eq_of_degreeOf_lt (p := (X 0 * X 1 : MvPolynomial (Fin 2) F))
      (q := 1) (i := i) (by simp [hprod])
    rw [factorPolynomial, add_comm, h, hprod]
    fin_cases i <;> rfl

private lemma factorPolynomial_ne_zero (a : Factor) : factorPolynomial F a ≠ 0 := by
  cases a with
  | trivial => exact one_ne_zero
  | natural => exact X_ne_zero 0
  | dual => exact X_ne_zero 1
  | adjoint =>
    apply ne_zero_of_degreeOf_ne_zero (i := 0)
    rw [degreeOf_factorPolynomial]
    decide

private lemma wordPolynomial_ne_zero (w : List Factor) : wordPolynomial F w ≠ 0 := by
  induction w with
  | nil => exact one_ne_zero
  | cons a w ih => exact mul_ne_zero (factorPolynomial_ne_zero F a) (pow_ne_zero _ ih)

private lemma degreeOf_wordPolynomial (w : List Factor) (i : Fin 2) :
    (wordPolynomial F w).degreeOf i = wordWeight w i := by
  induction w with
  | nil => simp [wordPolynomial, wordWeight]
  | cons a w ih =>
    rw [wordPolynomial, degreeOf_mul' F i (factorPolynomial_ne_zero F a)
      (pow_ne_zero _ (wordPolynomial_ne_zero F w)), degreeOf_factorPolynomial,
      degreeOf_sq F i _ (wordPolynomial_ne_zero F w), ih]
    rfl

private lemma wordWeight_lt (w : List Factor) (i : Fin 2) : wordWeight w i < 2 ^ w.length := by
  induction w with
  | nil => simp [wordWeight]
  | cons a w ih =>
    have h := factorDigit_le_one a i
    simp only [wordWeight, List.length_cons, pow_succ]
    omega

private lemma wordWeight_injective (v w : List Factor) (hlen : v.length = w.length)
    (hweight : ∀ i, wordWeight v i = wordWeight w i) : v = w := by
  induction v generalizing w with
  | nil => simpa using hlen.symm
  | cons a v ih =>
    cases w with
    | nil => simp at hlen
    | cons b w =>
      have h0 := hweight 0
      have h1 := hweight 1
      have hab : a = b := by
        cases a <;> cases b <;> simp_all [wordWeight, factorDigit] <;> omega
      subst b
      congr 1
      apply ih w (by simpa using hlen)
      intro i
      have hi := hweight i
      simp only [wordWeight] at hi
      omega

private lemma wordPolynomial_injective (v w : List Factor) (hlen : v.length = w.length)
    (hpoly : wordPolynomial F v = wordPolynomial F w) : v = w := by
  apply wordWeight_injective v w hlen
  intro i
  simpa only [degreeOf_wordPolynomial] using congrArg (degreeOf i) hpoly

private lemma polynomial_grid_zero [Fintype F] {n : ℕ} (p : MvPolynomial (Fin n) F)
    (hdegree : ∀ i, p.degreeOf i < Fintype.card F)
    (heval : ∀ x : Fin n → F, eval x p = 0) : p = 0 := by
  induction n with
  | zero =>
    apply (MvPolynomial.isEmptyRingEquiv F (Fin 0)).injective
    have h := heval (0 : Fin 0 → F)
    rw [MvPolynomial.eval_zero] at h
    rw [isEmptyRingEquiv_eq_coeff_zero, map_zero]
    exact h
  | succ n ih =>
    apply (finSuccEquiv F n).injective
    rw [map_zero]
    apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_zero]
    apply ih
    · intro i
      exact lt_of_le_of_lt (degreeOf_coeff_finSuccEquiv p i k) (hdegree i.succ)
    · intro x
      have h : Polynomial.map (eval x) (finSuccEquiv F n p) = 0 := by
        apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ Function.injective_id
        · intro y
          simpa only [id_eq, ← eval_eq_eval_mv_eval'] using heval (Fin.cons y x)
        · exact lt_of_le_of_lt Polynomial.natDegree_map_le
            ((natDegree_finSuccEquiv p).trans_lt (hdegree 0))
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using
        congrArg (fun q => Polynomial.coeff q k) h

/-- Evaluation on the entire finite-field grid distinguishes words of the prescribed length. -/
lemma word_eq_of_polynomial_eval_eq [Finite F] (n : ℕ)
    (hcard : Nat.card F = 2 ^ n) (v w : List Factor)
    (hv : v.length = n) (hw : w.length = n)
    (heval : ∀ x : Fin 2 → F, eval x (wordPolynomial F v) = eval x (wordPolynomial F w)) :
    v = w := by
  let := Fintype.ofFinite F
  apply wordPolynomial_injective F v w (hv.trans hw.symm)
  apply sub_eq_zero.mp
  apply polynomial_grid_zero F
  · intro i
    apply lt_of_le_of_lt (degreeOf_sub_le i (wordPolynomial F v) (wordPolynomial F w))
    rw [degreeOf_wordPolynomial, degreeOf_wordPolynomial, max_lt_iff,
      Fintype.card_eq_nat_card, hcard]
    exact ⟨by simpa [hv] using wordWeight_lt v i, by simpa [hw] using wordWeight_lt w i⟩
  · intro x
    simp only [map_sub, heval x, sub_self]

end Representation.SL3.BinaryDefiningFactors.TensorSimplicity.CharacterSeparation

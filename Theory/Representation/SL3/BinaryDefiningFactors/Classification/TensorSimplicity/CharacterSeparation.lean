module
public import Theory.Representation.SL3.BinaryDefiningFactors
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.RestrictedSeparation
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.CharacterSeparation.Polynomials
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.CharacterSeparation.FactorCharacters
public import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.FinCases

/-!
# Separation of the concrete binary SL₃ tensor words

An equivalence between two tensor words gives equality of their characters.
The factor character formulas and tensor multiplicativity identify each word
character with its polynomial evaluated at matrix trace and inverse trace.
A determinant-one companion matrix realizes every pair of field elements as
these two traces. Finite-grid interpolation therefore identifies the word
polynomials, whose degree pairs recover the words.

This proves the uniqueness part of GLS III, 2.8.2 and 2.8.6(a), for the concrete
SL₃ factors in 2.8.10(c). It uses no word irreducibility or completeness input.
The proof includes `|F| = 2` and works over any coefficient field of characteristic
two admitting the given embedding; algebraic closure is unnecessary.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped MatrixGroups
namespace Representation.SL3.BinaryDefiningFactors.TensorSimplicity.CharacterSeparation
variable {F K : Type*} [Field F] [Field K] [CharP K 2]

/-- Each actual restricted-factor character evaluates its two-variable polynomial. -/
lemma factorRep_character_polynomial (ι : F →+* K) (a : Factor) (g : SL(3,F)) :
    (factorRep ι a).character g =
      ι (MvPolynomial.eval ![Matrix.trace g.val, Matrix.trace g⁻¹.val] (factorPolynomial F a)) := by
  cases a with
  | trivial =>
    change LinearMap.trace K K 1 = _
    simp [factorPolynomial]
  | natural =>
    change (natural ι).character g = _
    rw [natural_character_trace]
    simp [factorPolynomial]
  | dual =>
    change (natural ι).dual.character g = _
    rw [Representation.char_dual, natural_character_trace]
    simp [factorPolynomial]
  | adjoint =>
    rw [adjoint_character]
    simp [factorPolynomial]

/-- The actual Frobenius tensor word has the recursively squared character polynomial. -/
lemma wordRep_character_polynomial (ι : F →+* K) (w : List Factor) (g : SL(3,F)) :
    (wordRep ι w).character g =
      ι (MvPolynomial.eval ![Matrix.trace g.val, Matrix.trace g⁻¹.val] (wordPolynomial F w)) := by
  induction w generalizing ι with
  | nil =>
    change LinearMap.trace K K 1 = _
    simp [wordPolynomial]
  | cons a w ih =>
    rw [wordRep, Representation.char_tensor, Pi.mul_apply, factorRep_character_polynomial, ih]
    simp [wordPolynomial, RingHom.comp_apply, frobenius_def]

private def companion (s t : F) : SL(3,F) :=
  ⟨!![0,0,1;1,0,t;0,1,s], by simp [Matrix.det_fin_three]⟩

private lemma companion_inv (s t : F) : (companion s t)⁻¹ =
    ⟨!![-t,1,0;-s,0,1;1,0,0], by simp [Matrix.det_fin_three]⟩ := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (!![0,0,1;1,0,t;0,1,s] : Matrix (Fin 3) (Fin 3) F) *
    !![-t,1,0;-s,0,1;1,0,0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- Equality of actual characters distinguishes words of the prescribed length. -/
lemma word_eq_of_character_eq [Finite F]
    (ι : F →+* K) (n : ℕ) (hcard : Nat.card F = 2 ^ n) (v w : List Factor)
    (hv : v.length = n) (hw : w.length = n)
    (hchar : (wordRep ι v).character = (wordRep ι w).character) : v = w := by
  let : CharP F 2 := ι.charP ι.injective 2
  apply word_eq_of_polynomial_eval_eq F n hcard v w hv hw
  intro x
  have h := congrFun hchar (companion (x 0) (x 1))
  rw [wordRep_character_polynomial, wordRep_character_polynomial] at h
  apply ι.injective
  have hx : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
  rw [companion_inv] at h
  simpa [companion, Matrix.trace_fin_three, CharTwo.neg_eq, hx] using h

end CharacterSeparation

variable {F K : Type*} [Field F] [Finite F] [Field K] [CharP K 2]

/-- An actual representation equivalence identifies the two tensor words. -/
lemma wordRep_equiv_imp_eq (ι : F →+* K) (n : ℕ) (hcard : Nat.card F = 2 ^ n)
    (v w : List Factor) (hv : v.length = n) (hw : w.length = n)
    (e : (wordRep ι v).Equiv (wordRep ι w)) : v = w :=
  CharacterSeparation.word_eq_of_character_eq ι n hcard v w hv hw (Representation.char_iso e)

/-- The concrete words of fixed field length have no repeated isomorphism types. -/
lemma wordRep_equiv_iff (ι : F →+* K) (n : ℕ) (hcard : Nat.card F = 2 ^ n)
    (v w : List Factor) (hv : v.length = n) (hw : w.length = n) :
    Nonempty ((wordRep ι v).Equiv (wordRep ι w)) ↔ v = w := by
  constructor
  · rintro ⟨e⟩
    exact wordRep_equiv_imp_eq ι n hcard v w hv hw e
  · rintro rfl
    exact ⟨Representation.Equiv.refl _⟩

end Representation.SL3.BinaryDefiningFactors.TensorSimplicity

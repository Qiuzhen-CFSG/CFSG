module

public import Theory.Representation.OrthogonalFourMinusFirstCohomology.Model
public import Theory.FieldTheory.QuadraticFrobeniusFixed
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Finite Hermitian matrices and their determinant form

Let `F = GF(2^(2n))` and let `k` be the actual fixed subfield of the
`n`-th Frobenius. For positive `n`, conjugation is involutive, `k` has
`2^n` elements, and `F` has dimension two over `k`.

The Hermitian matrices have explicit coordinates `(a,b,z)` in
`(k × k) × F`, corresponding to `!![a,z; conjugation z,b]`.
This proves dimension four. Their determinant is a `k`-valued quadratic
form, whose coordinate formula is `a*b - norm z`. The norm vanishes
only at zero. The previously constructed SL₂ action preserves this form.

These are the concrete field and coordinate foundations of the orthogonal
module in Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), Lemma I.1.6(3), printed p.408
(PDF p.419). Nonsingularity, the Witt index and the group identification
are proved separately from these definitions.
-/

@[expose] public section

noncomputable section
namespace Representation.OrthogonalFourMinus.FiniteModel
/-- The quadratic extension field, with its given Galois-field structure. -/
abbrev Field (n : ℕ) := GaloisField 2 (2 * n)

/-- The actual `2^n`-power Frobenius automorphism. -/
def conjugation (n : ℕ) : Field n ≃+* Field n := iterateFrobeniusEquiv (Field n) 2 n

/-- The fixed subfield inside the specified extension field. -/
def fixedField (n : ℕ) : Subfield (Field n) := FixedBy.subfield (Field n) (conjugation n)

lemma card_fixedField (n : ℕ) [NeZero n] : Nat.card (fixedField n) = 2 ^ n :=
  GaloisField.card_fixedBy_quadraticFrobenius 2 n (NeZero.ne n)

lemma conjugation_involutive (n : ℕ) [NeZero n] : Function.Involutive (conjugation n) := by
  intro x
  change iterateFrobeniusEquiv (Field n) 2 n (iterateFrobeniusEquiv (Field n) 2 n x) = x
  rw [← iterateFrobeniusEquiv_add_apply, iterateFrobeniusEquiv_def, ← two_mul]
  rw [← GaloisField.card 2 (2 * n) (Nat.mul_ne_zero (by decide) (NeZero.ne n))]
  let : Fintype (Field n) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card x

/-- Frobenius viewed as an automorphism over its actual fixed subfield. -/
def conjugationAlg (n : ℕ) : Field n ≃ₐ[fixedField n] Field n :=
  AlgEquiv.ofRingEquiv (f := conjugation n) (fun x => x.property)

lemma finrank_field (n : ℕ) [NeZero n] : Module.finrank (fixedField n) (Field n) = 2 := by
  have hcard := Module.natCard_eq_pow_finrank (K := fixedField n) (V := Field n)
  rw [card_fixedField, GaloisField.card 2 (2 * n) (Nat.mul_ne_zero (by decide) (NeZero.ne n)),
    show 2 ^ (2 * n) = (2 ^ n) ^ 2 by rw [← pow_mul, Nat.mul_comm n 2]] at hcard
  exact (pow_right_inj₀ (pow_pos (by decide : 0 < (2 : ℕ)) n)
    (Nat.one_lt_pow (NeZero.ne n) (by decide : 1 < (2 : ℕ))).ne').mp hcard.symm

/-- The Hermitian subspace of two-by-two matrices. -/
abbrev Space (n : ℕ) [NeZero n] : Type :=
  (hermitian (conjugationAlg n) (conjugation_involutive n)).toSubmodule

/-- The actual SL₂ action on the Hermitian matrix space. -/
def action (n : ℕ) [NeZero n] :
    Representation (fixedField n) (Matrix.SpecialLinearGroup (Fin 2) (Field n)) (Space n) :=
  hermitianAction (conjugationAlg n) (conjugation_involutive n)

lemma entry_fixed (n : ℕ) [NeZero n] (X : Space n) (i : Fin 2) :
    conjugation n (X.val i i) = X.val i i := congrFun (congrFun X.property i) i

lemma entry_conjugate (n : ℕ) [NeZero n] (X : Space n) (i j : Fin 2) :
    conjugation n (X.val j i) = X.val i j := congrFun (congrFun X.property i) j

/-- Two fixed diagonal entries and one arbitrary upper-right entry. -/
def coordinates (n : ℕ) [NeZero n] :
    Space n ≃ₗ[fixedField n] ((fixedField n × fixedField n) × Field n) where
  toFun X := ((⟨X.val 0 0, entry_fixed n X 0⟩, ⟨X.val 1 1, entry_fixed n X 1⟩), X.val 0 1)
  invFun v := ⟨!![v.1.1.val, v.2; conjugation n v.2, v.1.2.val], by
    ext i j
    fin_cases i <;> fin_cases j
    · exact v.1.1.property
    · exact conjugation_involutive n v.2
    · rfl
    · exact v.1.2.property⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    exact entry_conjugate n X 1 0
  right_inv v := by rfl
  map_add' X Y := by rfl
  map_smul' c X := by rfl

lemma finrank_space (n : ℕ) [NeZero n] : Module.finrank (fixedField n) (Space n) = 4 := by
  rw [(coordinates n).finrank_eq, Module.finrank_prod, Module.finrank_prod, finrank_field]
  simp

/-- Determinant with values in the actual fixed field. -/
def determinant (n : ℕ) [NeZero n] (X : Space n) : fixedField n :=
  ⟨X.val.det, det_fixed (conjugationAlg n) (conjugation_involutive n) X⟩

lemma determinant_smul (n : ℕ) [NeZero n] (c : fixedField n) (X : Space n) :
    determinant n (c • X) = (c * c) • determinant n X := by
  apply Subtype.ext
  simp [determinant, Subfield.smul_def, smul_eq_mul, pow_two]

/-- The determinant quadratic form, including in characteristic two. -/
def form (n : ℕ) [NeZero n] : QuadraticForm (fixedField n) (Space n) :=
  QuadraticMap.ofPolar (determinant n) (determinant_smul n)
    (by
      intro X Y Z
      apply Subtype.ext
      simp [QuadraticMap.polar, determinant, Matrix.det_fin_two]
      ring)
    (by
      intro c X Y
      apply Subtype.ext
      simp [QuadraticMap.polar, determinant, Matrix.det_fin_two, Matrix.smul_apply,
        Subfield.smul_def, smul_eq_mul]
      ring)

@[simp] lemma form_apply (n : ℕ) [NeZero n] (X : Space n) :
    form n X = determinant n X := rfl

lemma form_preserved (n : ℕ) [NeZero n] (A : Matrix.SpecialLinearGroup (Fin 2) (Field n))
    (X : Space n) : form n (action n A X) = form n X := by
  apply Subtype.ext
  exact det_hermitianAction (conjugationAlg n) (conjugation_involutive n) A X

/-- The norm into the actual fixed subfield. -/
def norm (n : ℕ) [NeZero n] (z : Field n) : fixedField n :=
  ⟨z * conjugation n z, by
    change conjugation n (z * conjugation n z) = z * conjugation n z
    rw [map_mul, conjugation_involutive]
    exact mul_comm _ _⟩

@[simp] lemma norm_eq_zero_iff (n : ℕ) [NeZero n] (z : Field n) :
    norm n z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have he : z * conjugation n z = 0 := congrArg Subtype.val h
    rcases mul_eq_zero.mp he with h | h
    · exact h
    · exact (conjugation n).injective (h.trans (map_zero _).symm)
  · rintro rfl
    apply Subtype.ext
    exact zero_mul _

lemma form_coordinates (n : ℕ) [NeZero n] (v : (fixedField n × fixedField n) × Field n) :
    form n ((coordinates n).symm v) = v.1.1 * v.1.2 - norm n v.2 := by
  apply Subtype.ext
  change ( !![v.1.1.val, v.2; conjugation n v.2, v.1.2.val] : Mat (Field n)).det = _
  rw [Matrix.det_fin_two]
  rfl

@[simp] lemma coe_form (n : ℕ) [NeZero n] (X : Space n) :
    (form n X : Field n) = X.val.det := rfl

@[simp] lemma coordinates_symm_val (n : ℕ) [NeZero n]
    (v : (fixedField n × fixedField n) × Field n) :
    ((coordinates n).symm v).val = !![v.1.1.val, v.2; conjugation n v.2, v.1.2.val] := rfl

lemma action_apply (n : ℕ) [NeZero n] (A : Matrix.SpecialLinearGroup (Fin 2) (Field n))
    (X : Space n) : (action n A X).val = A.val * X.val * adjoint (conjugation n) A.val := rfl

end Representation.OrthogonalFourMinus.FiniteModel

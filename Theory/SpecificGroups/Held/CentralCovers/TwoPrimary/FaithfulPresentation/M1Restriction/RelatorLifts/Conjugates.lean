module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.SourceRelations
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

/-!
# The Held source relations in conjugates of its involution

Write `a_n = y⁻ⁿ*x*yⁿ`. These are involutions, periodic with period seven;
the marked M₁ generators are `a₀, a₂, a₋₂`. Four of the source relators give
short words in the `a_n`. The remaining non-torsion source relator gives
`A = (y³)⁻¹`, where `A = a₀*a₋₁*...*a₋₁₆`. Thus `A⁷ = 1` and conjugation
by `A` shifts the indices by three. Every equation here is derived directly
in the original abstract presentation.

The source-word proofs expand the conjugates and cancel adjacent powers;
the shifted forms apply a group automorphism. The target-word translation
preserves multiplication order. In particular, target entry 5 is a conjugate
of entry 4. This module does not prove the remaining M₁ relators.

Source: John Bray's `HeG1-P1.M`, retained in `Held/Model/Source/`.
The frozen target words and marking are in `M1Restriction/Data.lean`.
-/

@[expose] public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.RelatorLifts
open Subgroup.CosetWordCertificate

/-- Right conjugation, with the same convention as the Magma source. -/
def conjugate (n : ℤ) : Presentation := (y ^ n)⁻¹ * x * y ^ n

/-- Products of positive letters in the conjugates of `x`. -/
def value (w : List ℤ) : Presentation := (w.map conjugate).prod

theorem conjugate_shift (n k : ℤ) :
    conjugate (n + k) = MulAut.conj ((y ^ k)⁻¹) (conjugate n) := by
  simp only [conjugate, zpow_add, MulAut.conj_apply, inv_inv]
  group

theorem conjugate_periodic (n : ℤ) : conjugate (n + 7) = conjugate n := by
  have hy : y ^ (7 : ℤ) = 1 := presentation_relations 1
  simp only [conjugate, zpow_add, hy, mul_one]

theorem conjugate_sq (n : ℤ) : conjugate n ^ 2 = 1 := by
  have h := congrArg (MulAut.conj ((y ^ n)⁻¹)) (presentation_relations 0)
  simpa only [relationWord, map_pow, map_one, MulAut.conj_apply, inv_inv,
    conjugate] using h

theorem value_shift (w : List ℤ) (k : ℤ) :
    value (w.map (fun n => n + k)) = MulAut.conj ((y ^ k)⁻¹) (value w) := by
  induction w with
  | nil => simp [value]
  | cons n w ih =>
    simpa only [value, List.map_cons, List.prod_cons, map_mul, conjugate_shift]
      using congrArg (fun z => conjugate (n + k) * z) ih

/-- The original marking of the three M₁ generators. -/
def markedIndex : Fin 3 → ℤ | 0 => 0 | 1 => 2 | 2 => -2

theorem liftedGenerator_eq_conjugate (i : Fin 3) :
    liftedGenerator i = conjugate (markedIndex i) := by
  fin_cases i <;> simp [liftedGenerator, markedIndex, conjugate]

theorem eval_positive (w : List (Fin 3)) :
    eval liftedGenerator (w.map (fun i => (i, true))) = value (w.map markedIndex) := by
  induction w with
  | nil => simp [value]
  | cons i w ih =>
    simpa only [List.map_cons, eval_cons, ↓reduceIte, value, List.prod_cons,
      liftedGenerator_eq_conjugate] using congrArg (fun z => conjugate (markedIndex i) * z) ih

/-- Source relators 3, 4, 5 and 6 (zero-based), rewritten in conjugates of `x`.
The last word is followed by `y⁷` in the original source relator. -/
def sourceIndices : Fin 4 → List ℤ
  | 0 => [0, 1, 2, 1, 2, 3, 2, 1, 2, 1]
  | 1 => [0, 3, 0, 3, 0, 3, 0, 3, 0, 3]
  | 2 => [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
  | 3 => [0, -1, -2, -3, -4, -6, -3, -4, -5, -4, -7, -5]

private theorem x_inv : x⁻¹ = x := inv_eq_of_mul_eq_one_left
  (by simpa only [relationWord, pow_two] using presentation_relations 0)

/-- The four even source relators, as actual equations in `Presentation`. -/
theorem source_value (i : Fin 4) : value (sourceIndices i) = 1 := by
  fin_cases i
  · have he : value (sourceIndices 0) = relationWord x y 3 := by
      simp only [value, sourceIndices, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, conjugate, relationWord, mul_inv_rev, x_inv]
      group
    exact he.trans (presentation_relations 3)
  · have he : value (sourceIndices 1) = relationWord x y 4 := by
      simp only [value, sourceIndices, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, conjugate, relationWord, x_inv, pow_succ, pow_zero]
      group
      simp [zpow_ofNat, pow_succ, mul_assoc]
    exact he.trans (presentation_relations 4)
  · have he : value (sourceIndices 2) = relationWord x y 5 := by
      simp only [value, sourceIndices, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, conjugate, relationWord, x_inv, pow_succ, pow_zero]
      group
    exact he.trans (presentation_relations 5)
  · have he : value (sourceIndices 3) * y ^ 7 = relationWord x y 6 := by
      simp only [value, sourceIndices, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, conjugate, relationWord, pow_succ, pow_zero]
      group
      simp [zpow_ofNat, pow_succ, mul_assoc]
    have hy : y ^ 7 = 1 := presentation_relations 1
    rw [hy, mul_one] at he
    exact he.trans (presentation_relations 6)

theorem conjugate_mod_seven (n : ℤ) : conjugate n = conjugate (n % 7) := by
  have hy : y ^ 7 = 1 := presentation_relations 1
  simpa [conjugate] using congrArg (fun z : Presentation => z⁻¹ * x * z)
    (zpow_eq_zpow_emod' n hy)

theorem source_value_shift (i : Fin 4) (k : ℤ) :
    value ((sourceIndices i).map (fun n => n + k)) = 1 := by
  rw [value_shift, source_value, map_one]

theorem relation_eq_value (i : Fin 12) :
    eval liftedGenerator (relationLetters i) = value ((relationIndices i).map markedIndex) :=
  eval_positive _

/-- Entries 4 and 5 differ by conjugation with `y²`. -/
theorem relation_five_of_four
    (h : eval liftedGenerator (relationLetters 4) = 1) :
    eval liftedGenerator (relationLetters 5) = 1 := by
  rw [relation_eq_value] at h ⊢
  have hs : value (((relationIndices 4).map markedIndex).map (fun n => n + (-2))) = 1 := by
    rw [value_shift, h, map_one]
  exact hs

/-- The conjugate factors of `(x*y)¹⁷` after moving powers of `y` to the right. -/
def seventeenIndices : List ℤ :=
  [0, -1, -2, -3, -4, -5, -6, -7, -8, -9, -10, -11, -12, -13, -14, -15, -16]

/-- This uses the odd source relator `(x*y)¹⁷ = 1`, together with `y⁷ = 1`.
It must be retained when deriving words of odd `x` parity. -/
theorem seventeen_value : value seventeenIndices = (y ^ 3)⁻¹ := by
  have he : value seventeenIndices * y ^ 17 = (x * y) ^ 17 := by
    simp only [value, seventeenIndices, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, conjugate, pow_succ, pow_zero]
    group
  have hy : y ^ 7 = 1 := presentation_relations 1
  have hy17 : y ^ 17 = y ^ 3 := by
    calc
      y ^ 17 = (y ^ 7) ^ 2 * y ^ 3 := by group
      _ = y ^ 3 := by rw [hy, one_pow, one_mul]
  apply eq_inv_of_mul_eq_one_left
  rw [← hy17, he]
  exact presentation_relations 2

theorem seventeen_pow_seven : value seventeenIndices ^ 7 = 1 := by
  rw [seventeen_value, inv_pow, ← pow_mul, show 3 * 7 = 7 * 3 from rfl, pow_mul]
  have hy : y ^ 7 = 1 := presentation_relations 1
  rw [hy, one_pow, inv_one]

theorem seventeen_conjugation (n : ℤ) :
    value seventeenIndices * conjugate n * (value seventeenIndices)⁻¹ =
      conjugate (n + 3) := by
  rw [conjugate_shift, seventeen_value]
  rfl

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.RelatorLifts

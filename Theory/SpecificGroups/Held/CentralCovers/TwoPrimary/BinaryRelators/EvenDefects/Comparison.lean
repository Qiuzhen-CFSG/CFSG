module
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.Normalization
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.CubicTriangle
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Comparison.Certificate
import Mathlib.Tactic.Group

/-!
# Equality of Held's square and sixth-power defects

The literal Schreier symbol 3 is `y²*x*y⁻²`. Set `a = g(3)⁻¹` and
`b = g(1772)⁻¹`. The checked central-tail replay proves
`b³ = r5*r6` and `(b*a)² = r5`, while direct conjugation gives `a² = r0`.
The central-involution cubic triangle then forces `r0 = r5`.

All words are evaluated in the arbitrary target group. No presentation
faithfulness, splitting, multiplier result, or vanishing defect is assumed.
The comparison leaves elimination of the common defect to its consumer.

Source words: John Bray's ATLAS `HeG1-P1.M`, retained in `Held/Model/Source/`.
The retained discovery slice, deterministic producer, and bounded kernel
checks are documented in `Comparison/source/README.md`.
-/

namespace Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects
open Comparison
variable {E : Type*} [Group E] {z x y : E}

private theorem square_of_symbol3 (h : Normalized z x y) :
    (symbolValue x y 3)⁻¹ ^ 2 = relationWord x y 0 := by
  have he : symbolValue x y 3 = y ^ 2 * x * (y ^ 2)⁻¹ := by
    simp only [symbolValue, FaithfulPresentation.M1Cosets.Schreier.symbolWord]
    change Subgroup.CosetWordCertificate.eval (generators x y)
      [(1, true), (1, true), (0, true), (1, false), (1, false)] = _
    simp [Subgroup.CosetWordCertificate.eval_cons, Subgroup.CosetWordCertificate.eval_nil,
      generators, pow_two, mul_assoc]
  have hp : symbolValue x y 3 ^ 2 = relationWord x y 0 := by
    rw [he, conj_pow]
    change y ^ 2 * relationWord x y 0 * (y ^ 2)⁻¹ = _
    rw [Subgroup.mem_center_iff.mp (defect_central h 0) _, mul_assoc, mul_inv_cancel, mul_one]
  rw [inv_pow, hp]
  exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using defect_square h 0)

/-- The square and sixth-power defects in the normalized ATLAS Held relators
are equal. This comparison does not assert that their common value is one. -/
public theorem square_eq_sixth_defect (z x y : E) (h : Normalized z x y) :
    relationWord x y 0 = relationWord x y 5 := by
  let a := (symbolValue x y 3)⁻¹
  let b := (symbolValue x y 1772)⁻¹
  have hb : b ^ 3 = relationWord x y 5 * relationWord x y 6 := by
    have hc := Certificate.cube h
    simpa [Theory.GroupTheory.CosetEnumeration.eval, Theory.GroupTheory.CosetEnumeration.letterValue,
      tails, tailCenter, maskBit, centralDefect, b, pow_succ, mul_assoc] using hc
  have hba : (b * a) ^ 2 = relationWord x y 5 := by
    have hc := Certificate.triangle h
    simpa [Theory.GroupTheory.CosetEnumeration.eval, Theory.GroupTheory.CosetEnumeration.letterValue,
      tails, tailCenter, maskBit, centralDefect, b, a, pow_two, mul_assoc] using hc
  apply (cubic_triangle a b (relationWord x y 5) (relationWord x y 0)
    (defect_central h 5) (defect_central h 0) (defect_square h 5) (defect_square h 0)
    (square_of_symbol3 h) hba ?_ ?_).symm
  · rw [hb]
    exact Subgroup.mul_mem _ (defect_central h 5) (defect_central h 6)
  · rw [show 6 = 3 * 2 from rfl, pow_mul, hb,
      (show Commute (relationWord x y 5) (relationWord x y 6) from
        Subgroup.mem_center_iff.mp (defect_central h 6) _).mul_pow,
      defect_square h 5, defect_square h 6, mul_one]

end Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects

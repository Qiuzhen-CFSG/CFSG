module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.Data
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

/-!
# The first four M₁ relations from the original seven relators

The three generators are conjugates of `x`, so they square to one. Conjugating
the source relation `[x,y³]⁵ = 1` by `y⁻²`, and using `y⁷ = 1`, gives the
fifth-power relation between the last two generators. These are identities
in the original abstract presentation, independent of its permutation image.

Source: John Bray's `Held/Model/Source/HeG1-P1.M`, relators 1, 2 and 5.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
open Subgroup.CosetWordCertificate

theorem liftedGenerator_sq (i : Fin 3) : liftedGenerator i ^ 2 = 1 := by
  have hx : x ^ 2 = 1 := presentation_relations 0
  fin_cases i
  · exact hx
  · simpa only [liftedGenerator, map_pow, map_one, MulAut.conj_apply, inv_inv] using
      congrArg (MulAut.conj ((y ^ 2)⁻¹)) hx
  · simpa only [liftedGenerator, map_pow, map_one, MulAut.conj_apply] using
      congrArg (MulAut.conj (y ^ 2)) hx

theorem last_pair_pow_five : (liftedGenerator 2 * liftedGenerator 1) ^ 5 = 1 := by
  have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_left
    (by simpa only [relationWord, pow_two] using presentation_relations 0)
  have hy : y ^ 4 = (y ^ 3)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [relationWord, ← pow_add] using presentation_relations 1
  have hrel : (x * (y ^ 3)⁻¹ * x * y ^ 3) ^ 5 = 1 := by
    simpa only [relationWord, hx] using presentation_relations 4
  have heq : (y ^ 2)⁻¹ * (x * (y ^ 3)⁻¹ * x * y ^ 3) * y ^ 2 =
      liftedGenerator 1 * liftedGenerator 2 := by
    have hy' : y ^ 3 = (y ^ 4)⁻¹ := by rw [hy, inv_inv]
    rw [← hy, hy']
    simp only [liftedGenerator]
    group
  have hc := congrArg (MulAut.conj ((y ^ 2)⁻¹)) hrel
  simp only [map_pow, map_one, MulAut.conj_apply, inv_inv, heq] at hc
  have hi := congrArg Inv.inv hc
  simpa only [liftedGenerator, ← inv_pow, mul_inv_rev, inv_inv, hx, inv_one,
    mul_assoc] using hi

/-- The first four entries of the frozen list follow from the original source. -/
theorem initial_relations (i : Fin 12) (hi : i.val < 4) :
    eval liftedGenerator (relationLetters i) = 1 := by
  fin_cases i
  · simpa only [relationLetters, relationIndices, List.map_cons, List.map_nil,
      eval_cons, eval_nil, Bool.true_eq, ↓reduceIte, mul_one, pow_two] using
      liftedGenerator_sq 2
  · simpa only [relationLetters, relationIndices, List.map_cons, List.map_nil,
      eval_cons, eval_nil, Bool.true_eq, ↓reduceIte, mul_one, pow_two] using
      liftedGenerator_sq 0
  · simpa only [relationLetters, relationIndices, List.map_cons, List.map_nil,
      eval_cons, eval_nil, Bool.true_eq, ↓reduceIte, mul_one, pow_two] using
      liftedGenerator_sq 1
  · simpa only [relationLetters, relationIndices, List.map_cons, List.map_nil,
      eval_cons, eval_nil, Bool.true_eq, ↓reduceIte, mul_one, pow_succ, pow_zero,
      one_mul, mul_assoc] using last_pair_pow_five
  all_goals simp at hi

/-- Only the remaining eight abstract word identities are still required. -/
theorem liftedRelations_of_remaining
    (h : ∀ i : Fin 12, 4 ≤ i.val → eval liftedGenerator (relationLetters i) = 1) :
    LiftedRelations := by
  intro i
  by_cases hi : i.val < 4
  · exact initial_relations i hi
  · exact h i (Nat.le_of_not_gt hi)

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction

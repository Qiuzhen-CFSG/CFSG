module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.Reduction
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.TransitionData
import Mathlib.Tactic.FinCases

/-!
# Soundness of the Held right-coset transition table

Positive generator transitions imply inverse transitions because their
index maps are permutations of the 135 representatives. Closure induction
then gives coverage of the actual local overgroup. Each right representative
is already a fixed double-coset representative times a word in the marking,
so the resulting cover is the required literal double-coset cover.

Only the positive word equalities remain explicit inputs here. In particular,
the numerical size 135 is not assumed to be the index of the marking.
Source: the generated factors in SubgroupCover/source/Generate.g.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover
open Subgroup

/-- Literal word equalities for the two positive local generators. -/
def PositiveTransitions : Prop :=
  ∀ (i : Bool) (r : Fin 135) (k : Fin 2),
    rightRepresentative i r * localLetter i (k.castLE (by decide)) =
      evalPowers (evenGenerator i) (transition i r (k.castLE (by decide))).2 *
        rightRepresentative i (transition i r (k.castLE (by decide))).1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private theorem inverse_index (i : Bool) (r : Fin 135) (k : Fin 2) :
    (transition i (transition i r ⟨k.val + 2, by omega⟩).1 (k.castLE (by decide))).1 = r := by
  cases i <;> fin_cases r <;> fin_cases k <;> decide +kernel

private theorem initial_eq (i : Bool) : rightRepresentative i 0 = 1 := by
  cases i <;> exact mul_one 1

private theorem inverse_step (hstep : PositiveTransitions) (i : Bool) (r : Fin 135)
    (k : Fin 2) : ∃ (h : He) (j : Fin 135), h ∈ candidateTwo i 0 ∧
      rightRepresentative i r * (localLetter i (k.castLE (by decide)))⁻¹ =
        h * rightRepresentative i j := by
  let j := (transition i r ⟨k.val + 2, by omega⟩).1
  let t := evalPowers (evenGenerator i) (transition i j (k.castLE (by decide))).2
  have ht : t ∈ candidateTwo i 0 := evalPowers_mem _ _ (evenGenerator_mem i) _
  have he := hstep i j k
  rw [inverse_index] at he
  refine ⟨t⁻¹, j, (candidateTwo i 0).inv_mem ht, ?_⟩
  have hh : t⁻¹ * (rightRepresentative i j * localLetter i (k.castLE (by decide))) =
      rightRepresentative i r := by rw [he]; exact inv_mul_cancel_left _ _
  rw [← hh, mul_assoc, mul_inv_cancel_right]

/-- Induction on the actual local generators certifies every double coset. -/
theorem doubleCosetCoverage_of_transitions (hstep : PositiveTransitions) :
    DoubleCosetCoverage := by
  intro i x hx
  have pos : ∀ (r : Fin 135) (y : He), y ∈ ({a, localWord i} : Set He) →
      ∃ (h : He) (j : Fin 135), h ∈ candidateTwo i 0 ∧
        rightRepresentative i r * y = h * rightRepresentative i j := by
    intro r y hy
    have step (k : Fin 2) : ∃ (h : He) (j : Fin 135), h ∈ candidateTwo i 0 ∧
        rightRepresentative i r * localLetter i (k.castLE (by decide)) =
          h * rightRepresentative i j :=
      ⟨evalPowers (evenGenerator i) (transition i r (k.castLE (by decide))).2,
        (transition i r (k.castLE (by decide))).1,
        evalPowers_mem _ _ (evenGenerator_mem i) _, hstep i r k⟩
    rcases hy with rfl | hy
    · exact step 0
    · rcases hy with rfl
      exact step 1
  have neg : ∀ (r : Fin 135) (y : He), y ∈ ({a, localWord i} : Set He) →
      ∃ (h : He) (j : Fin 135), h ∈ candidateTwo i 0 ∧
        rightRepresentative i r * y⁻¹ = h * rightRepresentative i j := by
    intro r y hy
    rcases hy with rfl | hy
    · exact inverse_step hstep i r 0
    · rcases hy with rfl
      exact inverse_step hstep i r 1
  have hc : ∃ (h : He) (r : Fin 135), h ∈ candidateTwo i 0 ∧
      x = h * rightRepresentative i r := by
    induction hx using closure_induction_right with
    | one => exact ⟨1, 0, (candidateTwo i 0).one_mem, by rw [initial_eq, one_mul]⟩
    | mul_right z _ y hy ih =>
      obtain ⟨h, r, hh, rfl⟩ := ih
      obtain ⟨t, j, ht, he⟩ := pos r y hy
      exact ⟨h * t, j, (candidateTwo i 0).mul_mem hh ht, by rw [mul_assoc, he, ← mul_assoc]⟩
    | mul_inv_cancel z _ y hy ih =>
      obtain ⟨h, r, hh, rfl⟩ := ih
      obtain ⟨t, j, ht, he⟩ := neg r y hy
      exact ⟨h * t, j, (candidateTwo i 0).mul_mem hh ht, by rw [mul_assoc, he, ← mul_assoc]⟩
  obtain ⟨h, r, hh, he⟩ := hc
  refine ⟨(rightData i r).1, h, evalPowers (evenGenerator i) (rightData i r).2,
    hh, evalPowers_mem _ _ (evenGenerator_mem i) _, ?_⟩
  simpa only [rightRepresentative, mul_assoc] using he

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover

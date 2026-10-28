module

public import Theory.SpecificGroups.Rudvalis.Model.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Tactic.Group

/-!
# Perfectness of the concrete Rudvalis group

In the abelianization, x = ab has fourth and thirteenth powers one, hence
x = 1. The word w = ababb then becomes b, whose fourth and twenty-ninth
powers are one. Thus both generators vanish in the abelianization.
Only the checked relations of the actual degree-4060 ATLAS model are used;
no complete-presentation or simplicity assertion is needed.
This supplies the perfect-base hypothesis in Aschbacher–Smith I.1.1–I.1.3,
printed p.407; the generator provenance is in `Model.PermutationData`.
-/

namespace Rudvalis
public instance model_isPerfect : Group.IsPerfect Model := by
  let q : Model →* Abelianization Model := Abelianization.of
  have ha : q a ^ 2 = 1 := by rw [← map_pow, a_sq, map_one]
  have hb : q b ^ 4 = 1 := by rw [← map_pow, b_fourth, map_one]
  have hab : (q a * q b) ^ 13 = 1 := by
    rw [← map_mul, ← map_pow, ab_thirteenth, map_one]
  have hab4 : (q a * q b) ^ 4 = 1 := by
    rw [mul_pow, show q a ^ 4 = (q a ^ 2) ^ 2 by rw [← pow_mul], ha, hb]
    simp
  have hx : q a * q b = 1 := by
    have h : (q a * q b) ^ 13 = q a * q b := by
      calc
        _ = ((q a * q b) ^ 4) ^ 3 * (q a * q b) := by rw [← pow_mul]; exact pow_succ _ 12
        _ = q a * q b := by rw [hab4]; simp
    exact h.symm.trans hab
  have hw : (q b) ^ 29 = 1 := by
    have hqw : q w = q b := by simp only [w, map_mul, hx, one_mul]
    rw [← hqw, ← map_pow, w_twentyNinth, map_one]
  have hb1 : q b = 1 := by
    have h : q b ^ 29 = q b := by
      calc
        _ = (q b ^ 4) ^ 7 * q b := by group
        _ = q b := by rw [hb]; simp
    exact h.symm.trans hw
  have ha1 : q a = 1 := by simpa only [hb1, mul_one] using hx
  refine ⟨eq_top_of_a_mem_of_b_mem (commutator Model) ?_ ?_⟩
  · rw [← Abelianization.ker_of]
    exact ha1
  · rw [← Abelianization.ker_of]
    exact hb1
end Rudvalis

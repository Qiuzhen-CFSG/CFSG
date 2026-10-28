module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Lifts.LiftedRelations.Geometry
import Mathlib.Tactic.FinCases

/-!
# Torus equivariance of the normalized lifts

Conjugating the defining commutator conjugates both preimages. The torus
centralizes every chosen inverter, so independence from preimages identifies
the new commutator with the appropriate power of the next normalized root.
The power identity uses only commutation of two elements with the same image
in a central extension. No order or exponent assumption on the kernel enters.

This supplies the actual torus action used in the exceptional root-relation
calculation for Aschbacher--Smith I.1.4(5), printed p.408; GLS3 §6.1.
-/

public noncomputable section
open scoped commutatorElement
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts.LiftedRelations
variable {E : Type*} [Group E] (f : E →* S) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E)
include hk in
private theorem commute_same_image (x y : E) (h : f x = f y) : Commute x y := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [CentralExtension.commutator_eq_of_image_eq f hk h rfl]
  exact (Commute.refl y).commutator_eq
private theorem commutator_pow (a b : E) (hc : Commute b ⁅a,b⁆) (n : ℕ) :
    ⁅a,b ^ n⁆ = ⁅a,b⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', commutatorElement_mul_right_eq_mul_conj, ih]
    rw [(hc.pow_right n).right_comm ⁅a,b⁆, mul_inv_cancel_right, pow_succ']

include hk in
/-- The canonical commutator lifts retain the full marked torus rotation. -/
theorem normalizedRoot_rotates (T : E) (hT : f T = torus 1) (r : Fin 6) :
    T * normalizedRoot f hf r * T⁻¹ =
      normalizedRoot f hf (rotatedRoot r) ^ rotationPower r := by
  let s := rotatedRoot r
  let a := (hf (torus (inverterIndex s))).choose
  let b := (hf (root s)).choose
  have ha : f a = torus (inverterIndex s) := (hf _).choose_spec
  have hb : f b = root s := (hf _).choose_spec
  have hc : Commute b ⁅a,b⁆ := by
    apply commute_same_image f hk
    rw [hb, ← normalizedRoot_eq_commutator f hf hk s a b ha hb]
    exact (normalizedRoot_projects_cube f hf hk s).1.symm
  have hi : inverterIndex r = inverterIndex s := by
    dsimp [s]
    fin_cases r <;> rfl
  calc
    T * normalizedRoot f hf r * T⁻¹ =
        ⁅T * (hf (torus (inverterIndex r))).choose * T⁻¹,
          T * (hf (root r)).choose * T⁻¹⁆ := conjugate_commutatorElement _ _ _
    _ = ⁅a, b ^ rotationPower r⁆ := by
      apply CentralExtension.commutator_eq_of_image_eq f hk
      · rw [map_mul, map_mul, map_inv, hT, (hf _).choose_spec, ha,
          (torus_commute 1 (inverterIndex r)).eq, mul_inv_cancel_right, hi]
      · rw [map_mul, map_mul, map_inv, map_pow, hT, (hf _).choose_spec, hb]
        exact torus_rotates r
    _ = ⁅a,b⁆ ^ rotationPower r := commutator_pow a b hc _
    _ = normalizedRoot f hf s ^ rotationPower r := by
      rw [normalizedRoot_eq_commutator f hf hk s a b ha hb]
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts.LiftedRelations

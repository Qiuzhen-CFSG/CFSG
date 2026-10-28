module

public import Theory.GroupTheory.PResidual.Quotient
public import Mathlib.GroupTheory.Perm.Sign

/-!
# A marked transposition outside the two-residual

For an actual isomorphism to S₄, the inverse image of `(0 1)` is an
involution outside the two-residual. The sign homomorphism has a two-group
target, so it kills the residual and detects this particular element.
No residual recognition theorem is assumed.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.9.9(3) and the final paragraph of Theorem 13.9.1, printed pp.973–974.
-/

public section

namespace Theory.SpecificGroups.SymmetricFour

variable {H : Type*} [Group H]

/-- The marked isomorphism transports sign, which kills the literal
two-residual of the original group. -/
theorem sign_eq_one_of_mem_twoResidual
    (e : H ≃* Equiv.Perm (Fin 4)) {x : H} (hx : x ∈ pResidual 2 H) :
    Equiv.Perm.sign (e x) = 1 := by
  have hsign : IsPGroup 2 ℤˣ := IsPGroup.of_card (n := 1)
    (by simp [Nat.card_eq_fintype_card, Fintype.card_units_int])
  exact Subgroup.pResidual_le_ker_of_isPGroup 2
    (Equiv.Perm.sign.comp e.toMonoidHom) hsign hx

/-- An explicit transposition lift, with both its order and residual escape. -/
theorem transposition_lift_outside_twoResidual
    (e : H ≃* Equiv.Perm (Fin 4)) :
    orderOf (e.symm (Equiv.swap (0 : Fin 4) 1)) = 2 ∧
      e.symm (Equiv.swap (0 : Fin 4) 1) ∉ pResidual 2 H := by
  constructor
  · rw [e.symm.orderOf_eq]
    apply orderOf_eq_prime
    · decide
    · decide
  · intro hx
    have hs := sign_eq_one_of_mem_twoResidual e hx
    rw [e.apply_symm_apply, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1)] at hs
    exact (by decide : (-1 : ℤˣ) ≠ 1) hs

end Theory.SpecificGroups.SymmetricFour

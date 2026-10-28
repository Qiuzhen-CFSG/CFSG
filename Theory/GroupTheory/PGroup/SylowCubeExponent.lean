module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.NormNum

/-!
# The order-nine obstruction from a cubic Sylow subgroup

If one Sylow three-subgroup has exponent dividing three, no element of the
ambient finite group has order divisible by nine. Extract an order-nine
power and embed its cyclic subgroup in a Sylow subgroup; Sylow conjugacy
then transports the exponent bound. This is used for the actual M₂₄ and
Rudvalis carriers in the local inspection of Aschbacher--Smith 4.3.16, p.618.
-/

public section
open Subgroup
namespace Subgroup
variable {A : Type*} [Group A] [Finite A]

/-- An exponent-three Sylow subgroup excludes nine from every element order. -/
theorem not_nine_dvd_orderOf_of_sylow_cube
    (P : Sylow 3 A) (hc : ∀ x : P, x ^ 3 = 1) (a : A) : ¬ 9 ∣ orderOf a := by
  intro ha
  let b := a ^ (orderOf a / 9)
  have hb : orderOf b = 9 := orderOf_pow_orderOf_div (orderOf_pos a).ne' ha
  have hz : IsPGroup 3 (zpowers b) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_zpowers,hb]; rfl)
  obtain ⟨Q,hQ⟩ := hz.exists_le_sylow
  let e := Q.equiv P
  have hpow : (⟨b,hQ (mem_zpowers b)⟩ : Q) ^ 3 = 1 := e.injective (by
    rw [map_pow,map_one]; exact hc _)
  have hd : 9 ∣ 3 := by
    rw [←hb]
    exact orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hpow)
  norm_num at hd

end Subgroup

module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.OddLocal.Three
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.OddLocal.Five
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Mathlib.GroupTheory.Sylow

/-!
# Actual odd Sylow configurations for the J₂ multiplier calculation

The checked subgroups of orders 27 and 25 have indices 22400 and 24192.
Their indices prove that they are Sylow subgroups of the original permutation
carrier. The marked inverter identities supply the local premises of the
central-cover transfer argument, with every element in that same carrier.

Source: Aschbacher–Smith I.1.3(1), printed p.407; GLS3 §6.1.
-/

public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.UpperBound.OddLocal
open Sporadic.LeechRelated.J2 Subgroup
open scoped commutatorElement

/-- An extraspecial Sylow three-subgroup with an ambient simultaneous inverter. -/
theorem exists_three_configuration :
    ∃ (Q : Sylow 3 Carrier) (x y r : Carrier),
      closure ({x, y} : Set Carrier) = (Q : Subgroup Carrier) ∧
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧
      Commute x ⁅x, y⁆ ∧ Commute y ⁅x, y⁆ ∧
      r * x * r⁻¹ = x⁻¹ ∧ r * y * r⁻¹ = y⁻¹ ∧ Commute r ⁅x, y⁆ := by
  have hi : ¬ 3 ∣ Three.P.index := by
    have h := Three.P.card_mul_index
    rw [Three.card_P, ExceptionalParabolics.FirstParabolic.card_carrier] at h
    have he : Three.P.index = 22400 := by omega
    rw [he]
    decide
  let hp : IsPGroup 3 Three.P := IsPGroup.of_card (n := 3) Three.card_P
  exact ⟨hp.toSylow hi, Three.x, Three.y, Three.r, rfl,
    Three.x_pow, Three.y_pow, Three.commutator_ne_one, Three.x_commute_commutator,
    Three.y_commute_commutator, Three.r_inverts_x, Three.r_inverts_y,
    Three.r_commute_commutator⟩

/-- An elementary Sylow five-subgroup with an ambient partial inverter. -/
theorem exists_five_configuration :
    ∃ (Q : Sylow 5 Carrier) (x y r : Carrier),
      closure ({x, y} : Set Carrier) = (Q : Subgroup Carrier) ∧
      x ^ 5 = 1 ∧ Commute x y ∧ r * x * r⁻¹ = x⁻¹ ∧ Commute r y := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hi : ¬ 5 ∣ Five.P.index := by
    have h := Five.P.card_mul_index
    rw [Five.card_P, ExceptionalParabolics.FirstParabolic.card_carrier] at h
    have he : Five.P.index = 24192 := by omega
    rw [he]
    decide
  let hp : IsPGroup 5 Five.P := IsPGroup.of_card (n := 2) Five.card_P
  exact ⟨hp.toSylow hi, Five.x, Five.y, Five.r, rfl,
    Five.x_pow, Five.x_commute_y, Five.r_inverts_x, Five.r_commute_y⟩

end Theory.SpecificGroups.J2HSMultipliers.J2.UpperBound.OddLocal

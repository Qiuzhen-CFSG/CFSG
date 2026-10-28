module
public import Theory.SpecificGroups.SymmetricFive.NoForty

/-!
# The five-point orbit obstruction

Orbit–stabilizer and the first isomorphism theorem would put a group of
order forty in S₅ if the faithful point stabilizer had order eight.
Source: the orbit step in Aschbacher–Smith 13.9.5, printed p.970.
-/

public section
open Subgroup
namespace MulAction
variable {K α : Type*} [Group K] [Finite K] [Finite α] [MulAction K α]

theorem orbit_card_ne_five_of_stabilizer_kernel_ratio (a : α)
    (h : Nat.card (stabilizer K a)=8*Nat.card (toPermHom K (orbit K a)).ker) :
    (orbit K a).ncard≠5 := by
  intro ho
  let ρ := toPermHom K (orbit K a)
  have hα : Nat.card (orbit K a)=5 := (Nat.card_coe_set_eq _).trans ho
  have hk := ρ.ker.card_mul_index
  rw [Subgroup.index_ker] at hk
  have hs := (stabilizer K a).card_mul_index
  rw [index_stabilizer,ho,h] at hs
  have hp : 0 < Nat.card ρ.ker := Nat.card_pos
  have hr : Nat.card ρ.range=40 := by nlinarith
  exact SymmetricFive.subgroup_card_ne_forty_of_card_five hα ρ.range hr
end MulAction

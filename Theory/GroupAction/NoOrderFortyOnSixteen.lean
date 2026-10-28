module
public import Theory.GroupAction.NormalFiveTwentyBound
public import Mathlib.GroupTheory.Sylow

/-!
# No faithful sixteen-element action of a group of order forty

Sylow counting makes the subgroup of order five normal. In a faithful
automorphism action on a group of order sixteen its centralizer has order
dividing fifteen. Since the acting group has no element of order fifteen,
the normal-five bound makes its order divide twenty, a contradiction.

The native M₂₃ heptad quotient uses this through its actual faithful A₇
action on the pointwise kernel of order sixteen. Source application:
Aschbacher–Smith 15.1.22(5), printed pp.1099–1100; GLS3 Table 5.3d.
-/

public section
open Subgroup
namespace Theory.GroupAction

/-- A group acting faithfully by automorphisms on sixteen elements
cannot have order forty. -/
theorem card_ne_forty_of_faithful_sixteen {H V : Type*}
    [Group H] [Finite H] [Group V] [Finite V]
    (f : H →* MulAut V) (hf : Function.Injective f) (hV : Nat.card V = 16) :
    Nat.card H ≠ 40 := by
  intro hc
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 H := Classical.choice inferInstance
  have hP : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity,hc]
    decide +kernel
  have hi : (P : Subgroup H).index = 8 := by
    have hh := (P : Subgroup H).card_mul_index
    rw [hP,hc] at hh
    omega
  have hn : Nat.card (Sylow 5 H) = 1 := by
    have hd := P.card_dvd_index
    rw [hi] at hd
    have hm := card_sylow_modEq_one 5 H
    have hb := Nat.le_of_dvd (by decide : 0 < 8) hd
    change Nat.card (Sylow 5 H) % 5 = 1 % 5 at hm
    interval_cases hn : Nat.card (Sylow 5 H) <;> omega
  let : Subsingleton (Sylow 5 H) := (Nat.card_eq_one_iff_unique.mp hn).1
  let : (P : Subgroup H).Normal := P.normal_of_subsingleton
  have hh := (Subgroup.normal_five_centralizer_and_card_bound f hf
    (P : Subgroup H) hP hV (by
      intro x hx
      have hd := orderOf_dvd_natCard x
      rw [hx,hc] at hd
      norm_num at hd)).2
  rw [hc] at hh
  norm_num at hh

end Theory.GroupAction

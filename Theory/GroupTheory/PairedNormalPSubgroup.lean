module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Tactic.Group

/-!
# Normal two-subgroups preserve independent factors with cubic elements

If an element of a two-group exchanges commuting disjoint factors, its
commutator with a cubic element in one factor has order dividing three.
When the cubic element normalizes the two-group, this commutator is trivial.
Disjointness would then make the cubic element trivial, a contradiction.

This is the factor-permutation obstruction in Aschbacher--Smith 14.6.9(l).
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- A two-group cannot exchange disjoint commuting factors when a nontrivial
cubic element in the first factor normalizes it. -/
theorem twoGroup_cannot_exchange_disjoint_of_cubic {G : Type*} [Group G] (K L W : Subgroup G)
    (hW : IsPGroup 2 W) (hd : Disjoint K L) (hc : K ≤ centralizer (L : Set G))
    (a : G) (ha : a ∈ K) (han : a ∈ normalizer (W : Set G))
    (ha3 : a ^ 3 = 1) (hane : a ≠ 1)
    (w : G) (hw : w ∈ W) : K.map (MulAut.conj w).toMonoidHom ≠ L := by
  intro he
  let y := w * a⁻¹ * w⁻¹
  have hy : y ∈ L := by
    rw [←he]
    exact mem_map_of_mem (MulAut.conj w).toMonoidHom (K.inv_mem ha)
  have hy3 : y ^ 3 = 1 := by
    change ((MulAut.conj w) a⁻¹) ^ 3 = 1
    rw [←map_pow,inv_pow,ha3,inv_one,map_one]
  have hcomm : Commute a y := (hc ha y hy).symm
  have hd3 : (a * y)^3 = 1 := by rw [hcomm.mul_pow,ha3,hy3,mul_one]
  have hdW : a * y ∈ W := by
    have hh := (mem_normalizer_iff.mp han w).mp hw
    convert W.mul_mem hh (W.inv_mem hw) using 1
    dsimp [y]
    group
  have hdone : a * y = 1 := by
    by_contra hn
    have hz : (⟨a*y,hdW⟩ : W) ≠ 1 := fun h => hn (congrArg Subtype.val h)
    have hv := hW.dvd_orderOf hz
    have hp : orderOf (⟨a*y,hdW⟩ : W) ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext hd3)
    have := hv.trans hp
    norm_num at this
  have haL : a ∈ L := by
    have hay : a = y⁻¹ := (eq_inv_iff_mul_eq_one).mpr hdone
    rw [hay]
    exact L.inv_mem hy
  exact hane (show a ∈ (⊥ : Subgroup G) from (disjoint_iff_inf_le.mp hd) ⟨ha,haL⟩)

end Theory.GroupTheory

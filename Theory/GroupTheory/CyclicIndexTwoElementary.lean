module
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic

/-!
# Elementary subgroups in groups with a cyclic subgroup of index two

If C is cyclic of index two and every element of E squares to one, then
E has at most four elements. The intersection E ∩ C is cyclic with exponent
dividing two, so has order at most two; its relative index in E divides
two. Multiplying these two bounds gives the result. No finiteness assumption
is required by the cardinal formulation.

This elementary bound is used to exclude a centralizing involution next to
a Klein four subgroup under semidihedral Sylow geometry, in the normal PSL2
faithfulness step of Alperin--Brauer--Gorenstein II.3, Proposition 4.
-/

namespace Subgroup
variable {G : Type*} [Group G]

public theorem card_le_four_of_pow_two_of_cyclic_index_two
    (C : Subgroup G) [IsCyclic C] (hC : C.index = 2)
    (E : Subgroup G) (hE : ∀ x : E, x ^ 2 = 1) : Nat.card E ≤ 4 := by
  let I : Subgroup G := E ⊓ C
  let : IsCyclic I := Subgroup.isCyclic_of_le (show I ≤ C from inf_le_right)
  have hIc : Nat.card I ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    apply Subtype.ext
    exact congrArg (fun y : E => (y : G)) (hE ⟨x, x.property.1⟩)
  have hIle : Nat.card I ≤ 2 := Nat.le_of_dvd (by decide) hIc
  let : C.Normal := C.normal_of_index_eq_two hC
  have hidx : I.relIndex E ∣ 2 := by
    change (E ⊓ C).relIndex E ∣ 2
    rw [inf_relIndex_left]
    exact hC ▸ C.relIndex_dvd_index_of_normal E
  have hidxle : I.relIndex E ≤ 2 := Nat.le_of_dvd (by decide) hidx
  have hm := (I.subgroupOf E).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show I ≤ E from inf_le_left)).toEquiv] at hm
  change Nat.card I * I.relIndex E = Nat.card E at hm
  nlinarith

end Subgroup

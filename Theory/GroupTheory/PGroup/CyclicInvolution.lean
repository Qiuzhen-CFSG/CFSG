module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The involution of a cyclic two-group

Every nontrivial subgroup of a finite cyclic 2-group contains its unique
involution. Consequently, a subgroup omitting that involution is disjoint
from the cyclic subgroup. These facts supply the cyclic intersection argument
in ABG Chapter II §1 Lemma 2(xiii), but use only general finite-group theory.

A nonidentity element in a 2-group has even order, and its half-order power
is an involution. The standard count of elements of order two in a cyclic
group establishes uniqueness, exported for arbitrary finite cyclic groups,
and identifies this power with the specified involution. The general
uniqueness API also identifies the mixed outer involution defining PGL*.
-/

/-- The involution in any finite cyclic group is unique. -/
public theorem IsCyclic.eq_of_orderOf_eq_two {G : Type*} [Group G] [Finite G] [IsCyclic G] {x y : G}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  classical
  let := Fintype.ofFinite G
  have hd : 2 ∣ Fintype.card G := by
    rw [← Nat.card_eq_fintype_card, ← hx]
    exact orderOf_dvd_natCard (x := x)
  have hc := IsCyclic.card_orderOf_eq_totient (α := G) hd
  simp only [Nat.totient_two] at hc
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  have hx' : x ∈ ({g : G | orderOf g = 2} : Finset G) := by simpa
  have hy' : y ∈ ({g : G | orderOf g = 2} : Finset G) := by simpa
  rw [ha, Finset.mem_singleton] at hx' hy'
  exact hx'.trans hy'.symm

namespace IsPGroup
variable {G : Type*} [Group G] [Finite G] [IsCyclic G]

public theorem involution_mem_subgroup_of_ne_bot (hG : IsPGroup 2 G)
    {x : G} (hx : orderOf x = 2) (H : Subgroup G) (hH : H ≠ ⊥) : x ∈ H := by
  classical
  obtain ⟨a, ha, hane⟩ := H.bot_or_exists_ne_one.resolve_left hH
  have ho : orderOf (a ^ (orderOf a / 2)) = 2 :=
    orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos a)) (hG.dvd_orderOf hane)
  rw [IsCyclic.eq_of_orderOf_eq_two hx ho]
  exact H.pow_mem ha _

end IsPGroup

namespace IsPGroup
variable {G : Type*} [Group G] [Finite G]

public theorem disjoint_of_involution_not_mem (hG : IsPGroup 2 G)
    (H K : Subgroup G) [IsCyclic H] {x : G} (hxH : x ∈ H)
    (hx : orderOf x = 2) (hxK : x ∉ K) : Disjoint H K := by
  apply Subgroup.disjoint_def.mpr
  intro a haH haK
  by_contra hane
  have hK : K.subgroupOf H ≠ ⊥ := by
    intro he
    have hm : (⟨a, haH⟩ : H) ∈ K.subgroupOf H := haK
    rw [he, Subgroup.mem_bot] at hm
    exact hane (congrArg Subtype.val hm)
  exact hxK ((hG.to_subgroup H).involution_mem_subgroup_of_ne_bot
    (x := ⟨x, hxH⟩) (by simpa using hx) (K.subgroupOf H) hK)
end IsPGroup

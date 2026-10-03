module

public import Theory.GroupTheory.PGroup.ExtraspecialInvolution
public import Theory.GroupTheory.Commutator.ElementaryCentralQuotient

/-!
# Squares in derived subgroups above an extraspecial core

Let a finite group have a normal extraspecial two-subgroup and abelian
quotient. Squares of elements in the derived subgroup of any subgroup lie
in the embedded center of that core, of order two. The subgroup generated
by these squares is characteristic. If the subgroup has no characteristic
subgroup of order two, all its derived elements therefore have square one.

This isolates the characteristic-line obstruction used with a fused normal
four. Source context: Janko–Thompson, Math. Z. 113 (1970), §4 case (b)(ii),
printed p.391, and the structural inputs 1.3–1.5 on p.386.
-/

open Subgroup

namespace Subgroup

/-- Without a characteristic subgroup of order two, an abelian extension of
an extraspecial core has no nontrivial squares in a subgroup's derived group. -/
public theorem derived_square_eq_one_of_no_characteristic_two_of_normal_extraspecial
    {T : Type*} [Group T] [Finite T]
    (H C : Subgroup T) [H.Normal] [IsExtraspecial 2 H]
    [IsMulCommutative (T ⧸ H)]
    (hchar : ∀ K : Subgroup C, K.Characteristic → Nat.card K ≠ 2)
    (x : C) (hx : x ∈ _root_.commutator C) : x ^ 2 = 1 := by
  let D : Subgroup C := closure {y : C | ∃ a ∈ _root_.commutator C, a ^ 2 = y}
  let : D.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro f
    apply (closure_le _).mpr
    rintro _ ⟨a, ha, rfl⟩
    change f (a ^ 2) ∈ D
    rw [map_pow]
    exact subset_closure ⟨f a, characteristic_iff_le_comap.mp inferInstance f ha, rfl⟩
  have hder : (_root_.commutator C).map C.subtype ≤ H := by
    rw [map_subtype_commutator]
    exact (commutator_mono le_top le_top).trans
      (Normal.quotient_commutative_iff_commutator_le.mp inferInstance)
  have hle : D.map C.subtype ≤ (center H).map H.subtype := by
    apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro _ ⟨a, ha, rfl⟩
    have haH : (a : T) ∈ H := hder (mem_map_of_mem C.subtype ha)
    exact ⟨(⟨a, haH⟩ : H) ^ 2, IsExtraspecial.square_mem_center _, rfl⟩
  have hbound : Nat.card D ≤ 2 := by
    have hh := card_le_of_le hle
    rwa [card_map_of_injective C.subtype_injective,
      card_map_of_injective H.subtype_injective, IsExtraspecial.center_order_p 2 H] at hh
  have hne := hchar D inferInstance
  have hcard : Nat.card D = 1 := by
    have hp := Nat.card_pos (α := D)
    omega
  have hxD : x ^ 2 ∈ D := subset_closure ⟨x, hx, rfl⟩
  rwa [card_eq_one.mp hcard, mem_bot] at hxD

end Subgroup

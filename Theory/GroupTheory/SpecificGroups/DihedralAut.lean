module

public import Theory.GroupTheory.CharacteristicIndexTwoAut
public import Theory.GroupTheory.CyclicTwoAut
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Automorphisms of dihedral two-groups

For rotation order greater than two, the rotation subgroup is characteristic:
its generator has order greater than two, whereas every reflection is an
involution. Its index is two, and restriction to this cyclic subgroup shows
that the automorphism group of a dihedral two-group is a two-group.
The order-four exception is deliberately excluded.

Source: the elementary dihedral calculation accompanying GLS2, Chapter C,
Sections 10.1–10.11.
-/

namespace DihedralGroup
open Subgroup

private theorem rotation_mem {m : ℕ} [NeZero m] (i : ZMod m) :
    r i ∈ zpowers (r 1 : DihedralGroup m) := by
  have h := pow_mem (mem_zpowers (r 1 : DihedralGroup m)) i.val
  simpa only [r_one_pow, ZMod.natCast_zmod_val] using h

/-- For rotation order greater than two the rotation subgroup is characteristic. -/
public theorem rotations_characteristic {m : ℕ} (hm : 2 < m) :
    (zpowers (r 1 : DihedralGroup m)).Characteristic := by
  let : NeZero m := ⟨by omega⟩
  apply characteristic_iff_le_comap.mpr
  intro f
  apply zpowers_le.mpr
  change f (r 1) ∈ zpowers (r 1 : DihedralGroup m)
  have hord := f.orderOf_eq (r 1)
  cases he : f (r 1) with
  | r i => exact rotation_mem i
  | sr i =>
    rw [he, orderOf_sr, orderOf_r_one] at hord
    omega

/-- A dihedral two-group of order greater than four has a two-group of automorphisms. -/
public theorem isPGroup_mulAut_of_two_lt {m : ℕ} (hm : 2 < m)
    (hD : IsPGroup 2 (DihedralGroup m)) : IsPGroup 2 (MulAut (DihedralGroup m)) := by
  let : NeZero m := ⟨by omega⟩
  let A := zpowers (r 1 : DihedralGroup m)
  let : A.Characteristic := rotations_characteristic hm
  have hc : Nat.card A = m := by rw [Nat.card_zpowers, orderOf_r_one]
  have hi : A.index = 2 := by
    have h := A.index_mul_card
    rw [hc, nat_card] at h
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < m) h
  exact A.isPGroup_mulAut_of_characteristic_index_two hi
    (hD.to_subgroup A) (hD.to_subgroup A).mulAut_of_isCyclic_two

end DihedralGroup

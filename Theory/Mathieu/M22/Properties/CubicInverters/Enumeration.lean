module

public import Theory.Mathieu.M22.Properties.CubicInverters.Certificates
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PartitionStructure
public import Theory.Mathieu.M22.Properties.Automorphisms

/-!
# Exhaustive cubic inversion in a Sylow subgroup of the M₂₂ design group

The marked pair and hexad-partition stabilizers have intersection of order 256.
Every certified local word lies in that intersection, and their distinct keys
make the map from 256 row indices bijective. This proves exhaustive coverage of
an actual Sylow two-subgroup. The row certificates then supply a cubic inverter
for every one of its involutions.

Source: the involution inversion step of Aschbacher–Smith H.12.1, printed p.394
(PDF p.405). The ambient transport is in the parent `CubicInverters` module.
-/

public section
namespace Sporadic.Mathieu.M22CubicInverters
open Subgroup M22ValueBound.Concrete
open scoped Pointwise
set_option maxRecDepth 100000

noncomputable def standardSylow : Sylow 2 m22DesignAut :=
  Sylow.ofCard (outerFirst ⊓ outerSecond) (by
    rw [PartitionStructure.outerIntersection_card, m22DesignAut_order]
    decide +kernel)

private theorem generator_mem (i : Fin 4) : generator i ∈ standardSylow := by
  change generator i ∈ outerFirst ⊓ outerSecond
  constructor
  · change Finset.image (fun x => (generator i).val x) m22Pair12 = m22Pair12
    simp only [generator_apply]
    revert i
    decide +kernel
  · change Finset.image (fun B => Finset.image (fun x => (generator i).val x) B)
      hexadPartition = hexadPartition
    simp only [generator_apply]
    revert i
    decide +kernel

private theorem localWord_mem (w : List (Fin 4)) : localWord w ∈ standardSylow := by
  induction w with
  | nil => exact (standardSylow : Subgroup m22DesignAut).one_mem
  | cons j w ih => exact (standardSylow : Subgroup m22DesignAut).mul_mem (generator_mem j) ih

theorem rowElement_apply (i : Fin 256) (x : Fin 22) :
    (rowElement i).val x = rowTable i x := by
  rw [rowElement, localWord_apply, row_word_table]

noncomputable def rowSylow (i : Fin 256) : standardSylow :=
  ⟨rowElement i, localWord_mem (rowWord i)⟩

private theorem rowSylow_injective : Function.Injective rowSylow := by
  intro i j h
  apply row_key_injective
  have he := congrArg (fun g : standardSylow =>
    (g.val.val 0).val * 22 ^ 2 + (g.val.val 1).val * 22 + (g.val.val 4).val) h
  simpa only [rowSylow, rowElement_apply] using he

theorem rowSylow_surjective : Function.Surjective rowSylow :=
  (rowSylow_injective.bijective_of_nat_card_le (by
    change Nat.card (outerFirst ⊓ outerSecond : Subgroup m22DesignAut) ≤ Nat.card (Fin 256)
    rw [PartitionStructure.outerIntersection_card, Nat.card_fin])).2

theorem cubicElement_apply (i : Fin 58) (x : Fin 22) :
    (cubicElement i).val x = cubicTable i x := by
  rw [cubicElement, innerWord_apply, cubic_word_table]

private theorem cubicElement_cube (i : Fin 58) : cubicElement i ^ 3 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (cubicElement i).val ((cubicElement i).val ((cubicElement i).val x)) = x
  simp only [cubicElement_apply]
  exact cubic_cube i x

theorem cubicElement_order (i : Fin 58) : orderOf (cubicElement i) = 3 := by
  apply orderOf_eq_prime (cubicElement_cube i)
  intro he
  have h := congrArg (fun y : M22 => y.val (cubicMovedPoint i)) he
  exact cubic_ne_one i ((cubicElement_apply i _).symm.trans h)

/-- Every involution in this actual Sylow subgroup has a certified cubic inverter. -/
theorem exists_inverted_three_of_mem_standard (s : m22DesignAut)
    (hs : orderOf s = 2) (hmem : s ∈ standardSylow) :
    ∃ y : M22, orderOf y = 3 ∧ m22DesignAutToAut s y = y⁻¹ := by
  obtain ⟨i, hi⟩ := rowSylow_surjective ⟨s, hmem⟩
  have he : rowElement i = s := congrArg Subtype.val hi
  subst s
  rcases row_cases i with hid | hsquare | hinv
  · have hrow : rowElement i = 1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro x
      exact (rowElement_apply i x).trans (hid x)
    simp [hrow] at hs
  · obtain ⟨x, hx⟩ := hsquare
    have hpow : rowElement i ^ 2 = 1 := hs ▸ pow_orderOf_eq_one (rowElement i)
    have h := congrArg (fun g : m22DesignAut => g.val x) hpow
    change (rowElement i).val ((rowElement i).val x) = x at h
    simp only [rowElement_apply] at h
    exact False.elim (hx h)
  · refine ⟨cubicElement (witness i), cubicElement_order _, ?_⟩
    have hpow : rowElement i ^ 2 = 1 := hs ▸ pow_orderOf_eq_one (rowElement i)
    have hself : (rowElement i)⁻¹ = rowElement i := by
      apply inv_eq_of_mul_eq_one_left
      exact hpow
    have hcube : cubicElement (witness i) ^ 2 = (cubicElement (witness i))⁻¹ := by
      apply eq_inv_iff_mul_eq_one.mpr
      rw [← pow_succ]
      exact cubicElement_cube _
    rw [← hcube]
    apply Subtype.ext
    rw [m22DesignAutToAut_apply_perm]
    have hself' := congrArg Subtype.val hself
    change (rowElement i).val⁻¹ = (rowElement i).val at hself'
    rw [hself']
    apply Equiv.ext
    intro x
    change (rowElement i).val ((cubicElement (witness i)).val ((rowElement i).val x)) =
      (cubicElement (witness i)).val ((cubicElement (witness i)).val x)
    simpa only [rowElement_apply, cubicElement_apply] using hinv x

end Sporadic.Mathieu.M22CubicInverters

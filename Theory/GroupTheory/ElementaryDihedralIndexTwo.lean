module
public import Theory.GroupTheory.PGroup.UniqueInvolution
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic.Linarith

/-!
# A unique involution in an elementary-by-dihedral product

An index-two subgroup of E × D₈ meets E × V₄ in index at most two.
If it has a unique involution, that elementary intersection has order at
most two. Hence E is trivial. The remaining subgroup has order four
and is cyclic by the elementary unique-involution argument.

This is the cyclic-four reduction in Aschbacher–Smith 2.4.36,
printed p.549 of the combined manuscript, 1 March 2004.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory

private def reflectionFour : Subgroup (DihedralGroup 4) where
  carrier := {a | a = 1 ∨ a = DihedralGroup.r 2 ∨ a = DihedralGroup.sr 0 ∨ a = DihedralGroup.sr 2}
  one_mem' := Or.inl rfl
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

private instance : DecidablePred (· ∈ reflectionFour) := fun a =>
  inferInstanceAs (Decidable (a = 1 ∨ a = DihedralGroup.r 2 ∨
    a = DihedralGroup.sr 0 ∨ a = DihedralGroup.sr 2))

private theorem reflectionFour_card : Nat.card reflectionFour = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem reflectionFour_square : ∀ a ∈ reflectionFour, a ^ 2 = 1 := by
  decide +kernel

/-- An index-two subgroup with a unique involution collapses an elementary
factor of a product with D₈, and is itself cyclic of order four. -/
theorem cyclic_four_of_unique_involution_in_elementary_dihedral
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (B : Subgroup (E × DihedralGroup 4)) (hi : B.index = 2)
    (hu : ∃! z : B, orderOf z = 2) :
    Nat.card E = 1 ∧ Nonempty (B ≃* Multiplicative (ZMod 4)) := by
  let A := (⊤ : Subgroup E).prod reflectionFour
  let W := (A ⊓ B).subgroupOf B
  have hp (w : W) : w ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) w.val.val.1
    · exact reflectionFour_square _ w.property.1.2
  let : IsElementaryAbelian 2 W :=
    { toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
        (fun w => orderOf_dvd_of_pow_eq_one (hp w)) a b).eq⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hp }
  have hW : Nat.card (A ⊓ B : Subgroup (E × DihedralGroup 4)) ≤ 2 := by
    have hw := card_elementary_le_two_of_unique_involution hu W
    rwa [Nat.card_congr (subgroupOfEquivOfLe
      (show A ⊓ B ≤ B from inf_le_right)).toEquiv] at hw
  let : B.Normal := B.normal_of_index_eq_two hi
  have hj : B.relIndex A ≤ 2 := Nat.le_of_dvd (by decide)
    (hi ▸ B.relIndex_dvd_index_of_normal A)
  have hmul : Nat.card (A ⊓ B : Subgroup (E × DihedralGroup 4)) * B.relIndex A = Nat.card A := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (E × DihedralGroup 4))
      (A ⊓ B) A bot_le inf_le_left
    simpa only [relIndex_bot_left, inf_relIndex_left] using hh
  have hA : Nat.card A = Nat.card E * 4 := by
    rw [Nat.card_congr (Subgroup.prodEquiv (⊤ : Subgroup E) reflectionFour).toEquiv,
      Nat.card_prod, card_top, reflectionFour_card]
  have hE : Nat.card E = 1 := by
    have hpE := Nat.card_pos (α := E)
    have hb : Nat.card A ≤ 4 := by nlinarith
    rw [hA] at hb
    omega
  have hB : Nat.card B = 4 := by
    have hm := B.card_mul_index
    rw [hi, Nat.card_prod, hE, DihedralGroup.nat_card] at hm
    omega
  let : IsMulCommutative B := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hB
  have hBp : IsPGroup 2 B := IsPGroup.of_card (n := 2) hB
  let : IsCyclic B := hBp.isCyclic_of_unique_involution_of_isMulCommutative hu
  refine ⟨hE, ⟨mulEquivOfCyclicCardEq ?_⟩⟩
  rw [hB, Nat.card_eq_fintype_card]
  rfl

/-- The same conclusion on a supplied product coordinate map. -/
theorem cyclic_four_of_unique_involution_index_two
    {H E : Type*} [Group H] [Finite H] [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (e : H ≃* (E × DihedralGroup 4))
    (B : Subgroup H) (hi : B.index = 2)
    (hu : ∃! z : B, orderOf z = 2) :
    Nat.card E = 1 ∧ Nonempty (B ≃* Multiplicative (ZMod 4)) := by
  let C := B.map e.toMonoidHom
  let eB : B ≃* C := e.subgroupMap B
  have hiC : C.index = 2 := (B.index_map_equiv e).trans hi
  have huC : ∃! z : C, orderOf z = 2 := by
    obtain ⟨z, hz, hu⟩ := hu
    refine ⟨eB z, (eB.orderOf_eq z).trans hz, ?_⟩
    intro a ha
    apply eB.symm.injective
    rw [eB.symm_apply_apply]
    exact hu _ ((eB.symm.orderOf_eq a).trans ha)
  obtain ⟨hE, ⟨eC⟩⟩ := cyclic_four_of_unique_involution_in_elementary_dihedral C hiC huC
  exact ⟨hE, ⟨eB.trans eC⟩⟩

end Theory.GroupTheory

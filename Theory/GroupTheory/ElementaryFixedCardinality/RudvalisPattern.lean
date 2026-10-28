module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The ten-two fixed-point obstruction for an elementary sixteen-group

Restrict an elementary binary subgroup of order sixteen to the ten points fixed
by a commuting element. If each of its fifteen nonidentity elements fixes two
of those points, Burnside's sum is forty, which is not divisible by sixteen.
The ambient action need not be faithful, and the ambient group need not be finite.

Source application: the Rudvalis row of Aschbacher--Smith 2.4.25, printed p.543.
The native cubic and involution pair counts are explicit inputs, proved by the
Rudvalis model's source owner.
-/

public section
open Subgroup
open scoped BigOperators
namespace Theory.GroupTheory

/-- The native ten-two pattern cannot coexist with a centralized elementary sixteen-group. -/
theorem elementary_sixteen_ten_two_fixed_pattern_false
    {D X : Type*} [Group D] [Finite X] [MulAction D X]
    (U : Subgroup D) [IsElementaryAbelian 2 U] (hU : Nat.card U = 16)
    (x : D) (_hx : orderOf x = 3) (hC : U ≤ centralizer ({x} : Set D))
    (hfix : Nat.card {i : X // x • i = i} = 10)
    (hpairs : ∀ u : D, orderOf u = 2 → Commute x u →
      Nat.card {i : X // x • i = i ∧ u • i = i} = 2) : False := by
  classical
  let : Finite U := Nat.finite_of_card_ne_zero (by rw [hU]; decide)
  let Y := {i : X // x • i = i}
  have hc (u : U) : Commute x u.val :=
    (mem_centralizer_singleton_iff.mp (hC u.property)).symm
  let : MulAction U Y := {
    smul u i := ⟨u.val • i.val, by
      rw [← mul_smul, (hc u).eq, mul_smul, i.property]⟩
    one_smul i := Subtype.ext (one_smul D i.val)
    mul_smul u v i := Subtype.ext (mul_smul u.val v.val i.val) }
  let : Fintype U := Fintype.ofFinite U
  let : Fintype Y := Fintype.ofFinite Y
  let : ∀ u : U, Fintype (MulAction.fixedBy Y u) := fun _ => Fintype.ofFinite _
  have hi (u : U) (hu : u ≠ 1) : Fintype.card (MulAction.fixedBy Y u) = 2 := by
    have ho : orderOf u.val = 2 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian u.val u.property)
        (fun he => hu (Subtype.ext he))
    let e : MulAction.fixedBy Y u ≃ {i : X // x • i = i ∧ u.val • i = i} := {
      toFun i := ⟨i.val.val, i.val.property, congrArg Subtype.val i.property⟩
      invFun i := ⟨⟨i.val, i.property.1⟩, Subtype.ext i.property.2⟩
      left_inv i := by cases i; rfl
      right_inv i := by cases i; rfl }
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e]
    exact hpairs u.val ho (hc u)
  have hid : Fintype.card (MulAction.fixedBy Y (1 : U)) = 10 := by
    let e : MulAction.fixedBy Y (1 : U) ≃ Y := {
      toFun i := i.val
      invFun i := ⟨i, one_smul U i⟩
      left_inv i := by cases i; rfl
      right_inv i := rfl }
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e]
    exact hfix
  have hsum : (∑ u : U, Fintype.card (MulAction.fixedBy Y u)) = 40 := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset U) _ (Finset.mem_univ (1 : U))]
    have hs : (∑ u ∈ (Finset.univ : Finset U).erase 1,
        Fintype.card (MulAction.fixedBy Y u)) =
        ∑ _u ∈ (Finset.univ : Finset U).erase 1, 2 := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hi u (Finset.mem_erase.mp hu).1
    rw [hs, hid]
    simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (1 : U)),
      Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, hU]
  have hUc : Fintype.card U = 16 := by simpa only [Nat.card_eq_fintype_card] using hU
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group U Y
  rw [hsum, hUc] at hb
  have hd : 16 ∣ 40 := hb ▸ dvd_mul_left _ _
  exact (by decide : ¬ 16 ∣ 40) hd

end Theory.GroupTheory

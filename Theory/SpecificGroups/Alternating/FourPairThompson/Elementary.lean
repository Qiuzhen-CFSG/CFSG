module
public import Theory.SpecificGroups.Alternating.FourPairThompson.Core
public import Theory.ElementaryAbelian.Quotient
import Mathlib.Tactic
/-!
# Large elementary subgroups lie in the wreath base

An elementary subgroup meeting the swapping coset has a subgroup of index
at most two in the base. Commutation with a swapping actor makes evaluation
in one coordinate injective on that subgroup. Its order is at most four,
so the original elementary subgroup has order at most eight.
This is the rank obstruction used in Aschbacher–Smith 14.1.10, printed p.978.
-/
@[expose] public section
namespace AlternatingFourPair.Thompson
open Subgroup Theory.GroupTheory
abbrev swapIndex : Q := Multiplicative.ofAdd (1 : ZMod 2)
theorem index_cases (i : Q) : i = 1 ∨ i = swapIndex := by revert i; decide +kernel
@[simp] theorem swapIndex_inv : swapIndex⁻¹ = swapIndex := by decide
@[simp] theorem swapIndex_sq : swapIndex * swapIndex = 1 := by decide
@[simp] theorem swapIndex_ne_one : swapIndex ≠ 1 := by decide

def evaluation (E : Subgroup W) (hb : E ≤ base) (i : Q) : E →* D where
  toFun x := x.val.left i
  map_one' := rfl
  map_mul' x y := by simp [show x.val.right = 1 from hb x.property]

 theorem base_eq_of_commute_left (t a b : W) (ht : t.right ≠ 1)
    (ha : a.right = 1) (hb : b.right = 1)
    (hat : Commute a t) (hbt : Commute b t) (hab : a.left 1 = b.left 1) : a = b := by
  have htr : t.right = swapIndex := (index_cases _).resolve_left ht
  have hA : a.left 1 * t.left 1 = t.left 1 * a.left swapIndex := by
    simpa [ha, htr] using congrArg (fun w : W => w.left 1) hat.eq
  have hB : b.left 1 * t.left 1 = t.left 1 * b.left swapIndex := by
    simpa [hb, htr] using congrArg (fun w : W => w.left 1) hbt.eq
  have hab' : a.left swapIndex = b.left swapIndex := by
    apply mul_left_cancel (a := t.left 1)
    rw [← hA, ← hB, hab]
  apply RegularWreathProduct.ext
  · funext i
    rcases index_cases i with rfl | rfl
    · exact hab
    · exact hab'
  · exact ha.trans hb.symm

private theorem subgroup_elementary {G : Type*} [Group G] [IsElementaryAbelian 2 G]
    (P : Subgroup G) : IsElementaryAbelian 2 P where
  is_comm.comm x y := Subtype.ext (IsMulCommutative.is_comm.comm x.val y.val)
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
    Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 G) x.val))

 theorem elementary_card_le_four_of_injective {G : Type*} [Group G] [Finite G]
    [IsElementaryAbelian 2 G] (f : G →* D) (hf : Function.Injective f) : Nat.card G ≤ 4 := by
  have he : IsElementaryAbelian 2 f.range := IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  exact symmetricFour_elementary_card_le f.range he

 theorem elementary_card_le_eight_of_not_base (E : Subgroup W)
    (hE : IsElementaryAbelian 2 E) (hn : ¬ E ≤ base) : Nat.card E ≤ 8 := by
  let _ := hE
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hn
  let f : E →* Q := (RegularWreathProduct.rightHom : W →* Q).comp E.subtype
  let v : f.ker →* D := {
    toFun x := x.val.val.left 1
    map_one' := rfl
    map_mul' x y := by
      have hx : x.val.val.right = 1 := x.property
      simp [hx] }
  have hv : Function.Injective v := by
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    apply base_eq_of_commute_left t a.val.val b.val.val htn a.property b.property
    · exact congrArg Subtype.val (IsMulCommutative.is_comm.comm a.val (⟨t, ht⟩ : E))
    · exact congrArg Subtype.val (IsMulCommutative.is_comm.comm b.val (⟨t, ht⟩ : E))
    · exact hab
  let : IsElementaryAbelian 2 f.ker := subgroup_elementary _
  have hk : Nat.card f.ker ≤ 4 := elementary_card_le_four_of_injective v hv
  have hr : f.ker.index ≤ 2 := by
    rw [index_ker]
    exact f.range.card_le_card_group.trans_eq (by norm_num [Nat.card_eq_fintype_card])
  rw [← f.ker.card_mul_index]
  exact (Nat.mul_le_mul hk hr).trans_eq (by norm_num)

 theorem elementary_le_base_of_card (E : Subgroup W)
    (hE : IsElementaryAbelian 2 E) (hc : 16 ≤ Nat.card E) : E ≤ base := by
  by_contra hn
  have := elementary_card_le_eight_of_not_base E hE hn
  omega
end AlternatingFourPair.Thompson

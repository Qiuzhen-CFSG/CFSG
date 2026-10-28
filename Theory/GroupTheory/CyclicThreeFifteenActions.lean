module
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-!
# Two involutory actions on a cyclic group of order three or fifteen

If the first action fixes exactly three elements and the second inverts an
element of order three, the numbers inverted by the second action and by
their product add to six or eighteen. A cyclic-group equivalence transports
the actions to scalar multiplication on `ZMod 3` or `ZMod 15`. The two tiny
scalar calculations are checked by the kernel; no ambient group is enumerated.

Source: Bender, *Finite groups with large subgroups* (1974), §4, printed
pp.225–226, the cyclic-action count underlying assertion (4.2).
-/

namespace MulAut

set_option synthInstance.maxSize 256 in
private theorem three_table : ∀ k l c : ZMod 3,
    k * k = 1 → l * l = 1 → c ≠ 0 → 3 * c = 0 → l * c = -c →
    Fintype.card {a : ZMod 3 // k * a = a} = 3 →
    Fintype.card {a : ZMod 3 // l * a = -a} +
      Fintype.card {a : ZMod 3 // (k * l) * a = -a} = 6 := by decide +kernel

set_option synthInstance.maxSize 256 in
private theorem fifteen_table : ∀ k l c : ZMod 15,
    k * k = 1 → l * l = 1 → c ≠ 0 → 3 * c = 0 → l * c = -c →
    Fintype.card {a : ZMod 15 // k * a = a} = 3 →
    Fintype.card {a : ZMod 15 // l * a = -a} +
      Fintype.card {a : ZMod 15 // (k * l) * a = -a} = 18 := by decide +kernel

private theorem scalar_action {A : Type*} [Group A] {n : ℕ} [NeZero n]
    (e : Multiplicative (ZMod n) ≃* A) (α : MulAut A) :
    ∃ k : ZMod n, ∀ a : ZMod n,
      α (e (Multiplicative.ofAdd a)) = e (Multiplicative.ofAdd (k * a)) := by
  let k := (e.symm (α (e (Multiplicative.ofAdd 1)))).toAdd
  refine ⟨k, fun a => ?_⟩
  have ha : Multiplicative.ofAdd a = (Multiplicative.ofAdd (1 : ZMod n)) ^ a.val := by
    change a = a.val • (1 : ZMod n)
    simp [nsmul_eq_mul]
  rw [ha, map_pow, map_pow]
  have hk : α (e (Multiplicative.ofAdd 1)) = e (Multiplicative.ofAdd k) := by
    exact (e.apply_symm_apply (α (e (Multiplicative.ofAdd 1)))).symm
  rw [hk, ← map_pow]
  apply congrArg e
  change Multiplicative.ofAdd (a.val • k) = Multiplicative.ofAdd (k * a)
  simp [nsmul_eq_mul, mul_comm]

private theorem model_fixed_count {A : Type*} [Group A] {n : ℕ} [NeZero n]
    (e : Multiplicative (ZMod n) ≃* A) (α : MulAut A) (k : ZMod n)
    (hk : ∀ a : ZMod n, α (e (Multiplicative.ofAdd a)) =
      e (Multiplicative.ofAdd (k * a))) :
    Nat.card {a : A // α a = a} = Fintype.card {a : ZMod n // k * a = a} := by
  classical
  let ee : ZMod n ≃ A :=
    { toFun := fun a => e (Multiplicative.ofAdd a)
      invFun := fun a => (e.symm a).toAdd
      left_inv := fun a => e.symm_apply_apply (Multiplicative.ofAdd a)
      right_inv := fun a => e.apply_symm_apply a }
  let ef := ee.subtypeEquiv (p := fun a => k * a = a) (q := fun a => α a = a)
    (fun a => by
      change k * a = a ↔ α (e (Multiplicative.ofAdd a)) = e (Multiplicative.ofAdd a)
      rw [hk, e.injective.eq_iff]
      rfl)
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr ef).symm

private theorem model_inverted_count {A : Type*} [Group A] {n : ℕ} [NeZero n]
    (e : Multiplicative (ZMod n) ≃* A) (α : MulAut A) (k : ZMod n)
    (hk : ∀ a : ZMod n, α (e (Multiplicative.ofAdd a)) =
      e (Multiplicative.ofAdd (k * a))) :
    Nat.card {a : A // α a = a⁻¹} = Fintype.card {a : ZMod n // k * a = -a} := by
  classical
  let ee : ZMod n ≃ A :=
    { toFun := fun a => e (Multiplicative.ofAdd a)
      invFun := fun a => (e.symm a).toAdd
      left_inv := fun a => e.symm_apply_apply (Multiplicative.ofAdd a)
      right_inv := fun a => e.apply_symm_apply a }
  let ef := ee.subtypeEquiv (p := fun a => k * a = -a) (q := fun a => α a = a⁻¹)
    (fun a => by
      change k * a = -a ↔ α (e (Multiplicative.ofAdd a)) = (e (Multiplicative.ofAdd a))⁻¹
      rw [hk, ← map_inv, e.injective.eq_iff]
      rfl)
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr ef).symm

/-- In the cyclic groups of orders three and fifteen, two involutory
actions give total inversion counts six and eighteen when the first has
three fixed points and the second inverts an element of order three. -/
public theorem inverted_card_sum_of_cyclic_three_fifteen {A : Type*} [Group A] [Finite A] [IsCyclic A]
    (hcard : Nat.card A = 3 ∨ Nat.card A = 15) (α β : MulAut A)
    (hα : α * α = 1) (hβ : β * β = 1)
    (hfixed : Nat.card {a : A // α a = a} = 3)
    (x : A) (hx : orderOf x = 3) (hβx : β x = x⁻¹) :
    Nat.card {a : A // β a = a⁻¹} + Nat.card {a : A // (α * β) a = a⁻¹} =
      if Nat.card A = 3 then 6 else 18 := by
  classical
  let n := Nat.card A
  let : NeZero n := ⟨Nat.card_pos.ne'⟩
  let e : Multiplicative (ZMod n) ≃* A := zmodCyclicMulEquiv (inferInstance : IsCyclic A)
  obtain ⟨k, hk⟩ := scalar_action e α
  obtain ⟨l, hl⟩ := scalar_action e β
  have hkl (a : ZMod n) : (α * β) (e (Multiplicative.ofAdd a)) =
      e (Multiplicative.ofAdd ((k * l) * a)) := by
    change α (β _) = _
    rw [hl, hk, mul_assoc]
  have hsquare (f : MulAut A) (q : ZMod n)
      (hf : f * f = 1) (hq : ∀ a : ZMod n,
        f (e (Multiplicative.ofAdd a)) = e (Multiplicative.ofAdd (q * a))) : q * q = 1 := by
    have hh := DFunLike.congr_fun hf (e (Multiplicative.ofAdd 1))
    change f (f (e (Multiplicative.ofAdd 1))) = e (Multiplicative.ofAdd 1) at hh
    rw [hq, mul_one, hq] at hh
    exact congrArg Multiplicative.toAdd (e.injective hh)
  have hk2 := hsquare α k hα hk
  have hl2 := hsquare β l hβ hl
  let c := (e.symm x).toAdd
  have hxc : x = e (Multiplicative.ofAdd c) := (e.apply_symm_apply x).symm
  have hc0 : c ≠ 0 := by
    intro hc
    have hx1 : x = 1 := by rw [hxc, hc]; exact e.map_one
    simp only [hx1, orderOf_one] at hx
    contradiction
  have hc3 : 3 * c = 0 := by
    have hh := congrArg e.symm (hx ▸ pow_orderOf_eq_one x)
    simp only [map_pow, map_one] at hh
    change 3 • c = 0 at hh
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hh
  have hlc : l * c = -c := by
    rw [hxc, hl, ← map_inv] at hβx
    exact congrArg Multiplicative.toAdd (e.injective hβx)
  have hkfixed : Fintype.card {a : ZMod n // k * a = a} = 3 :=
    (model_fixed_count e α k hk).symm.trans hfixed
  rw [model_inverted_count e β l hl, model_inverted_count e (α * β) (k * l) hkl]
  have table (m : ℕ) (hm : m = 3 ∨ m = 15) [NeZero m]
      (k l c : ZMod m) (hk2 : k * k = 1) (hl2 : l * l = 1)
      (hc0 : c ≠ 0) (hc3 : 3 * c = 0) (hlc : l * c = -c)
      (hkfixed : Fintype.card {a : ZMod m // k * a = a} = 3) :
      Fintype.card {a : ZMod m // l * a = -a} +
        Fintype.card {a : ZMod m // (k * l) * a = -a} =
          if m = 3 then 6 else 18 := by
    rcases hm with rfl | rfl
    · exact three_table k l c hk2 hl2 hc0 hc3 hlc hkfixed
    · exact fifteen_table k l c hk2 hl2 hc0 hc3 hlc hkfixed
  exact table n hcard k l c hk2 hl2 hc0 hc3 hlc hkfixed

end MulAut

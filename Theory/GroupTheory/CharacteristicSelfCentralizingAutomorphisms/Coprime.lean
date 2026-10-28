module
public import Theory.GroupTheory.CharacteristicSelfCentralizingAutomorphisms
public import Mathlib.GroupTheory.Perm.Finite
/-!
# Detecting coprime automorphisms on a small characteristic subgroup

For a self-centralizing characteristic p-subgroup C, the restriction kernel
on automorphisms is a p-group. An automorphism killed by n therefore vanishes
when n is coprime both to p and to |C|!: its permutation on C is trivial,
and then its membership in the restriction kernel removes the remaining action.

This is the automorphism calculation used for the A₃-block obstruction in
Aschbacher--Smith 14.6.15, printed p.1034.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
/-- A coprime automorphism is detected on the underlying set of C. -/
theorem automorphism_eq_one_of_characteristic_card (C : Subgroup G) [C.Characteristic] {p n : ℕ}
    (hp : IsPGroup p C) (hc : centralizer (C : Set G) ≤ C)
    (hnp : Nat.Coprime n p) (hnc : Nat.Coprime n (Nat.card C).factorial)
    (α : MulAut G) (hα : α ^ n = 1) : α = 1 := by
  classical
  let : Fintype C := Fintype.ofFinite C
  let f := MulAut.characteristic C
  let g := MulAut.toPerm C
  have hg : g (f α) = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes hnc
    · exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, ← map_pow, hα, map_one, map_one])
    · have hd := orderOf_dvd_natCard (g (f α))
      simpa only [Nat.card_eq_fintype_card, Fintype.card_perm] using hd
  have hf : f α = 1 := by
    apply MulEquiv.ext
    intro x
    exact congrArg (fun e : Equiv.Perm C => e x) hg
  have hk := C.isPGroup_characteristic_restriction_kernel_of_centralizer_le hp hc
  let a : f.ker := ⟨α,hf⟩
  have ha : a ^ n = 1 := Subtype.ext hα
  have hone : a = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hk.orderOf_coprime hnp.symm a) dvd_rfl
      (orderOf_dvd_of_pow_eq_one ha))
  exact congrArg Subtype.val hone
end Theory.GroupTheory

module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Three-point lines are separated by their pointwise kernels

A permutation of three points fixing two distinct points is trivial. Thus,
for a group fixing a base point and preserving each incident three-point
line, the pointwise kernel on a line through a second point is precisely
that point's stabilizer in the group. If these kernels distinguish the
incident lines, two distinct points lie on at most one such line.

This is the action argument used in Aschbacher–Smith I.5.8(1), using the
local kernels established in I.5.7. It uses no ambient recognition theorem.
-/

public section
namespace Equiv.Perm

private theorem fin_three_fix_two : ∀ (f : Equiv.Perm (Fin 3)) (x y : Fin 3),
    x ≠ y → f x = x → f y = y → f = 1 := by
  decide

theorem eq_one_of_card_three_of_two_fixed {X : Type*} (hc : Nat.card X = 3)
    (f : Equiv.Perm X) {x y : X} (hxy : x ≠ y) (hx : f x = x) (hy : f y = y) :
    f = 1 := by
  let : Finite X := Nat.finite_of_card_ne_zero (hc ▸ by decide)
  let := Fintype.ofFinite X
  let e := Fintype.equivFinOfCardEq (show Fintype.card X = 3 by
    simpa only [Nat.card_eq_fintype_card] using hc)
  let p : Equiv.Perm (Fin 3) := e.symm.trans (f.trans e)
  have hp : p = 1 := fin_three_fix_two p (e x) (e y) (e.injective.ne hxy)
    (by simpa only [p, Equiv.trans_apply, Equiv.symm_apply_apply] using congrArg e hx)
    (by simpa only [p, Equiv.trans_apply, Equiv.symm_apply_apply] using congrArg e hy)
  apply Equiv.ext
  intro z
  have h := Equiv.congr_fun hp (e z)
  apply e.injective
  simpa only [p, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.Perm.one_apply] using h

end Equiv.Perm

namespace MulAction
variable {G X L : Type*} [Group G] [MulAction G X]

/-- A three-point subset preserved by g is fixed pointwise once two points are fixed. -/
theorem fixes_three_point_set (A : Set X) (hcard : Nat.card A = 3) (g : G)
    (hpres : ∀ z, z ∈ A ↔ g • z ∈ A)
    {x y : X} (hxA : x ∈ A) (hyA : y ∈ A) (hxy : x ≠ y)
    (hx : g • x = x) (hy : g • y = y) : ∀ z ∈ A, g • z = z := by
  let f : Equiv.Perm A := {
    toFun z := ⟨g • z.val, (hpres z.val).mp z.property⟩
    invFun z := ⟨g⁻¹ • z.val, (hpres _).mpr (by
      simpa only [smul_inv_smul] using z.property)⟩
    left_inv z := Subtype.ext (inv_smul_smul g z.val)
    right_inv z := Subtype.ext (smul_inv_smul g z.val) }
  have he : f = 1 := Equiv.Perm.eq_one_of_card_three_of_two_fixed hcard f
    (x := ⟨x, hxA⟩) (y := ⟨y, hyA⟩) (fun h => hxy (congrArg Subtype.val h))
    (Subtype.ext hx) (Subtype.ext hy)
  intro z hz
  exact congrArg Subtype.val (Equiv.congr_fun he ⟨z, hz⟩)

/-- Distinct pointwise kernels force uniqueness of three-point lines through a fixed point. -/
theorem line_unique_of_kernel_separation (inc : X → L → Prop) (Q : Subgroup G)
    (x : X)
    (hcard : ∀ l, inc x l → Nat.card {z : X // inc z l} = 3)
    (hfix : ∀ g ∈ Q, g • x = x)
    (hpres : ∀ l, inc x l → ∀ g ∈ Q, ∀ z, inc z l ↔ inc (g • z) l)
    (hsep : ∀ l m, inc x l → inc x m →
      Q ⊓ fixingSubgroup G {z | inc z l} = Q ⊓ fixingSubgroup G {z | inc z m} → l = m)
    {y : X} (hxy : x ≠ y) {l m : L}
    (hxl : inc x l) (hyl : inc y l) (hxm : inc x m) (hym : inc y m) : l = m := by
  have hkernel (k : L) (hxk : inc x k) (hyk : inc y k) :
      Q ⊓ fixingSubgroup G {z | inc z k} = Q ⊓ stabilizer G y := by
    ext g
    constructor
    · intro h
      exact ⟨h.1, (mem_fixingSubgroup_iff G).mp h.2 y hyk⟩
    · intro h
      refine ⟨h.1, (mem_fixingSubgroup_iff G).mpr ?_⟩
      exact fixes_three_point_set _ (hcard k hxk) g (hpres k hxk g h.1)
        hxk hyk hxy (hfix g h.1) h.2
  exact hsep l m hxl hxm ((hkernel l hxl hyl).trans (hkernel m hxm hym).symm)

end MulAction

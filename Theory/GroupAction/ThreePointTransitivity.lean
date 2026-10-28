module

public import Theory.GroupAction.ThreePointKernelSeparation

/-!
# A nontrivial action on the other two points of a three-point set

A permutation of a three-point set which fixes one point and is not the
identity exchanges the remaining two. Thus any group preserving that set,
fixing the first point and acting nontrivially is transitive on the other
two points. This is the action step in I.5.7(2,4).
-/

public section
namespace Equiv.Perm

private theorem fin_three_exchange : ∀ (f : Equiv.Perm (Fin 3)) (x y z : Fin 3),
    x ≠ y → x ≠ z → y ≠ z → f x = x → f ≠ 1 → f y = z := by decide

theorem apply_eq_of_card_three {X : Type*} (hc : Nat.card X = 3)
    (f : Equiv.Perm X) {x y z : X} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : f x = x) (hf : f ≠ 1) : f y = z := by
  let : Finite X := Nat.finite_of_card_ne_zero (hc ▸ by decide)
  let := Fintype.ofFinite X
  let e := Fintype.equivFinOfCardEq (show Fintype.card X = 3 by
    simpa only [Nat.card_eq_fintype_card] using hc)
  let p : Equiv.Perm (Fin 3) := e.symm.trans (f.trans e)
  have hp : p ≠ 1 := by
    intro h
    apply hf
    apply Equiv.ext
    intro a
    apply e.injective
    simpa only [p, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.Perm.one_apply]
      using Equiv.congr_fun h (e a)
  have h := fin_three_exchange p (e x) (e y) (e z)
    (e.injective.ne hxy) (e.injective.ne hxz) (e.injective.ne hyz)
    (by simpa only [p, Equiv.trans_apply, Equiv.symm_apply_apply] using congrArg e hx) hp
  apply e.injective
  simpa only [p, Equiv.trans_apply, Equiv.symm_apply_apply] using h

end Equiv.Perm

namespace MulAction
variable {G X : Type*} [Group G] [MulAction G X]

theorem transitive_other_two_of_nontrivial (A : Set X) (hc : Nat.card A = 3)
    (Q : Subgroup G) {x : X} (hx : x ∈ A)
    (hfix : ∀ g ∈ Q, g • x = x)
    (hpres : ∀ g ∈ Q, ∀ z, z ∈ A ↔ g • z ∈ A)
    (hmove : ¬ Q ≤ fixingSubgroup G A)
    {y z : X} (hy : y ∈ A) (hz : z ∈ A) (hxy : x ≠ y) (hxz : x ≠ z) :
    ∃ g ∈ Q, g • y = z := by
  classical
  by_cases hyz : y = z
  · exact ⟨1, Q.one_mem, by simpa only [one_smul] using hyz⟩
  obtain ⟨g, hg, hn⟩ := SetLike.not_le_iff_exists.mp hmove
  let f : Equiv.Perm A := {
    toFun a := ⟨g • a.val, (hpres g hg a.val).mp a.property⟩
    invFun a := ⟨g⁻¹ • a.val, (hpres g⁻¹ (Q.inv_mem hg) a.val).mp a.property⟩
    left_inv a := Subtype.ext (inv_smul_smul g a.val)
    right_inv a := Subtype.ext (smul_inv_smul g a.val) }
  have hf : f ≠ 1 := by
    intro h
    apply hn
    apply (mem_fixingSubgroup_iff G).mpr
    intro a ha
    exact congrArg Subtype.val (Equiv.congr_fun h ⟨a, ha⟩)
  have h := Equiv.Perm.apply_eq_of_card_three hc f
    (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) (z := ⟨z, hz⟩)
    (fun h => hxy (congrArg Subtype.val h)) (fun h => hxz (congrArg Subtype.val h))
    (fun h => hyz (congrArg Subtype.val h)) (Subtype.ext (hfix g hg)) hf
  exact ⟨g, hg, congrArg Subtype.val h⟩

end MulAction

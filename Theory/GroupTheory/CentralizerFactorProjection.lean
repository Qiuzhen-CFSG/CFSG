module
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

/-!
# Projection onto the centralizer of a centerless factor

If every ambient conjugation on a centerless subgroup is inner, multiplication
identifies the group with that subgroup times its centralizer. The second
projection is surjective, kills exactly the original subgroup, and fixes every
original centralizer element. The construction uses actual inner implementers.

Source: the normal-factor splitting in Aschbacher--Smith, proof of 12.9.5,
printed p.861; this is an elementary internal direct-product construction.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {X : Type*} [Group X]

/-- The centralizer is an actual quotient factor, with its inclusion split. -/
theorem centralizer_projection_of_inner (N : Subgroup X)
    (hd : Disjoint N (centralizer (N : Set X)))
    (hi : ∀ x : X, ∃ n : N, x * (n : X)⁻¹ ∈ centralizer (N : Set X)) :
    ∃ π : X →* centralizer (N : Set X),
      Function.Surjective π ∧ π.ker = N ∧
      ∀ c : centralizer (N : Set X), π c.val = c := by
  let C := centralizer (N : Set X)
  let f : N × C →* X := N.subtype.noncommCoprod C.subtype
    (fun n c => (c.property n n.property : (n : X) * c = c * n))
  have hinj : Function.Injective f := by
    apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
    simpa only [range_subtype] using And.intro N.subtype_injective
      (And.intro C.subtype_injective hd)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨n,hn⟩ := hi x
    refine ⟨(n,⟨x * (n : X)⁻¹,hn⟩),?_⟩
    change (n : X) * (x * (n : X)⁻¹) = x
    rw [hn n n.property,inv_mul_cancel_right]
  let e := MulEquiv.ofBijective f ⟨hinj,hsurj⟩
  let π : X →* C := (MonoidHom.snd N C).comp e.symm.toMonoidHom
  have hp (n : N) (c : C) : π ((n : X) * c) = c := by
    change (e.symm (e (n,c))).2 = c
    rw [e.symm_apply_apply]
  have hc (c : C) : π c.val = c := by simpa only [OneMemClass.coe_one,one_mul] using hp 1 c
  refine ⟨π,fun c => ⟨c,hc c⟩,?_,hc⟩
  ext x
  obtain ⟨⟨n,c⟩,rfl⟩ := hsurj x
  change π ((n : X) * c) = 1 ↔ (n : X) * c ∈ N
  rw [hp,mul_mem_cancel_left n.property]
  constructor
  · intro h; simpa only [h,OneMemClass.coe_one] using N.one_mem
  · intro h
    exact Subtype.ext (hd.le_bot ⟨h,c.property⟩)
end Subgroup

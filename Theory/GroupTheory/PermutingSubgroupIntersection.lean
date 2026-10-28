module
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Restricting a subgroup product while retaining one factor

If D lies in N, membership of d*t in N is exactly membership of t
in N. Thus a set product can be intersected with N by intersecting
its other factor; no normality or order hypothesis is needed.

Source application: the original quintic actor in the component
stabilizer in Aschbacher--Smith 6.1.4, printed p.665.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- Both orders of the product restrict to a subgroup containing D. -/
theorem set_products_intersection_of_left_le (D T N : Subgroup G) (hDN : D ≤ N) :
    (D : Set G) * ((T ⊓ N : Subgroup G) : Set G) = ((D : Set G) * T) ∩ N ∧
    ((T ⊓ N : Subgroup G) : Set G) * (D : Set G) = ((T : Set G) * D) ∩ N := by
  constructor
  · ext x
    constructor
    · rintro ⟨d,hd,t,ht,rfl⟩
      exact ⟨⟨d,hd,t,ht.1,rfl⟩,N.mul_mem (hDN hd) ht.2⟩
    · rintro ⟨⟨d,hd,t,ht,rfl⟩,hN⟩
      exact ⟨d,hd,t,⟨ht,(N.mul_mem_cancel_left (hDN hd)).mp hN⟩,rfl⟩
  · ext x
    constructor
    · rintro ⟨t,ht,d,hd,rfl⟩
      exact ⟨⟨t,ht.1,d,hd,rfl⟩,N.mul_mem ht.2 (hDN hd)⟩
    · rintro ⟨⟨t,ht,d,hd,rfl⟩,hN⟩
      exact ⟨t,⟨ht,(N.mul_mem_cancel_right (hDN hd)).mp hN⟩,d,hd,rfl⟩

end Theory.GroupTheory

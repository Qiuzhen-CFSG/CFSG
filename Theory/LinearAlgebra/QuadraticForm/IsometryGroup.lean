module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# The group of linear isometries of a quadratic form

The full isometry group is the subgroup of linear automorphisms preserving
quadratic values. Keeping the quadratic values, rather than just the polar
form, is essential in characteristic two. This is the usual definition of
the orthogonal group; multiplication is composition of its actual linear maps.
-/

public section

namespace QuadraticMap
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def isometrySubgroup (q : QuadraticForm R V) : Subgroup (V ≃ₗ[R] V) where
  carrier := {g | ∀ v, q (g v) = q v}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro a b ha hb v
    exact (ha (b v)).trans (hb v)
  inv_mem' := by
    intro a ha v
    have h := ha (a.symm v)
    simpa only [LinearEquiv.apply_symm_apply, LinearEquiv.coe_inv] using h.symm

@[simp] theorem mem_isometrySubgroup (q : QuadraticForm R V) (g : V ≃ₗ[R] V) :
    g ∈ q.isometrySubgroup ↔ ∀ v, q (g v) = q v := Iff.rfl

end QuadraticMap


module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Permutations inducing a prescribed group on named points

For a map `point : X → Y` and a permutation group `H` on `X`, the
permutations of `Y` intertwining `point` with an element of `H` form a subgroup.
In particular generator identities extend to every word, including inverses.
No injectivity or coverage of `point` is needed for this upper-bound argument.

This elementary restriction argument is used for the fixed-letter action of
the Fi23 involution centralizer in GLS3, Table 5.3u. It supplies no assertion
that a proposed family generates that centralizer.
-/

@[expose] public section

namespace Theory.GroupAction

variable {X Y : Type*}

/-- Permutations of `Y` inducing an element of `H` along `point`. -/
def permutationLiftSubgroup (point : X → Y) (H : Subgroup (Equiv.Perm X)) :
    Subgroup (Equiv.Perm Y) where
  carrier := {g | ∃ p ∈ H, ∀ x, g (point x) = point (p x)}
  one_mem' := ⟨1, H.one_mem, fun _ => rfl⟩
  mul_mem' := by
    rintro g h ⟨p, hp, ep⟩ ⟨q, hq, eq⟩
    refine ⟨p * q, H.mul_mem hp hq, ?_⟩
    intro x
    simp only [Equiv.Perm.mul_apply, eq, ep]
  inv_mem' := by
    rintro g ⟨p, hp, ep⟩
    refine ⟨p⁻¹, H.inv_mem hp, ?_⟩
    intro x
    apply g.injective
    simpa using (ep (p⁻¹ x)).symm

theorem mem_permutationLiftSubgroup_iff (point : X → Y)
    (H : Subgroup (Equiv.Perm X)) (g : Equiv.Perm Y) :
    g ∈ permutationLiftSubgroup point H ↔
      ∃ p ∈ H, ∀ x, g (point x) = point (p x) := Iff.rfl

/-- A finite or infinite family of checked intertwiners controls its entire
generated subgroup. Inverse words require no further coordinate checks. -/
theorem closure_le_permutationLiftSubgroup (point : X → Y)
    (H : Subgroup (Equiv.Perm X)) (S : Set (Equiv.Perm Y))
    (hS : ∀ g ∈ S, ∃ p ∈ H, ∀ x, g (point x) = point (p x)) :
    Subgroup.closure S ≤ permutationLiftSubgroup point H :=
  (Subgroup.closure_le _).mpr hS

end Theory.GroupAction

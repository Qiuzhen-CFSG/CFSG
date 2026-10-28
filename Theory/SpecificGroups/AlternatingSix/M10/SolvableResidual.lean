module

public import Theory.SpecificGroups.AlternatingSix.M10.Action.Extension
public import Theory.GroupTheory.SolvableResidual

/-!
# The perfect residual in the actual M₁₀

The inner A₆ is perfect and has cyclic quotient of order two, so it is the
solvable residual. Cubic elements have trivial image in that quotient.
These statements retain the specified inner subgroup and its equivalence
to the alternating group on six letters.

Source: Aschbacher–Smith, J.2.7, printed pp.435,437 (PDF pp.446,448).
-/

@[expose] public section
open Subgroup
namespace AlternatingSix.M10
open ShadowLocal
/-- The restricted inner automorphism subgroup, identified with its actual A₆. -/
noncomputable def innerInExtensionEquiv : (inner.subgroupOf extension) ≃* A6 :=
  (subgroupOfEquivOfLe Action.inner_le_extension).trans innerEquiv.symm

/-- The actual inner subgroup has index two in M₁₀. -/
theorem innerInExtension_index : (inner.subgroupOf extension).index = 2 := by
  have h := (inner.subgroupOf extension).card_mul_index
  rw [Nat.card_congr innerInExtensionEquiv.toEquiv, card_A6, Action.card_extension] at h
  omega

/-- The solvable residual of the specified M₁₀ is its inner A₆. -/
theorem residual_eq_inner : solvableResidual extension = inner.subgroupOf extension := by
  let : Group.IsPerfect A6 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (inner.subgroupOf extension) :=
    Group.IsPerfect.ofSurjective (f := innerInExtensionEquiv.symm.toMonoidHom)
      innerInExtensionEquiv.symm.surjective
  let : IsCyclic (extension ⧸ inner.subgroupOf extension) :=
    isCyclic_of_prime_card innerInExtension_index
  let : Group.IsSolvable (extension ⧸ inner.subgroupOf extension) :=
    Group.isSolvable_of_comm fun x y => mul_comm' x y
  apply le_antisymm (solvableResidual_le_of_solvable_quotient _) (le_solvableResidual_of_isPerfect _)

/-- Elements whose cube is one belong to the inner A₆. -/
theorem cube_mem_inner (x : extension) (hx : x ^ 3 = 1) : x ∈ inner.subgroupOf extension := by
  let q := QuotientGroup.mk' (inner.subgroupOf extension)
  have h2 : q x ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := q x)
    change q x ^ (inner.subgroupOf extension).index = 1 at h
    rwa [innerInExtension_index] at h
  have h3 : q x ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  have hxq : q x = 1 := by simpa only [pow_succ, h2, one_mul] using h3
  exact (QuotientGroup.eq_one_iff x).mp hxq
end AlternatingSix.M10


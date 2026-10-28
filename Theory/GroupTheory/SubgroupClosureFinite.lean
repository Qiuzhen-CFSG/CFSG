module

public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Bounds for generated subgroups from transition tables

An indexed family containing the identity and stable under right multiplication
by each generator contains the generated subgroup, provided the transitions
have explicit right inverses. Inverse-generator stability follows by cancellation;
no second collection of group equations is needed. Finite instances give small,
kernel-checked certificates of nonmembership without enumerating subgroup lattices.

Source: the right-handed subgroup closure induction principle in Mathlib.
-/

namespace Theory.GroupTheory.SubgroupEnumeration

/-- Forward transitions and inverse index transitions bound the generated subgroup
by the range of the enumerated family. No distinctness assumption is needed. -/
public theorem closure_range_subset_range_of_transitions {G : Type*} [Group G] {ι κ : Type*}
    (s : ι → G) (r : κ → G) (base : κ) (next prev : κ → ι → κ)
    (hbase : r base = 1)
    (hn : ∀ a i, r a * s i = r (next a i))
    (hp : ∀ a i, next (prev a i) i = a) :
    (Subgroup.closure (Set.range s) : Set G) ⊆ Set.range r := by
  intro x hx
  apply Subgroup.closure_induction_right (p := fun x _ => x ∈ Set.range r) _ _ _ hx
  · exact ⟨base, hbase⟩
  · rintro x _ _ ⟨i, rfl⟩ ⟨a, rfl⟩
    exact ⟨next a i, (hn a i).symm⟩
  · rintro x _ _ ⟨i, rfl⟩ ⟨a, rfl⟩
    refine ⟨prev a i, ?_⟩
    have h := hn (prev a i) i
    rw [hp] at h
    exact eq_mul_inv_iff_mul_eq.mpr h


end Theory.GroupTheory.SubgroupEnumeration

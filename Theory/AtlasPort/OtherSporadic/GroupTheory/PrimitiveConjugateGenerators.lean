/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/PrimitiveConjugateGenerators.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Simplicity from primitive conjugate generators

In a faithful primitive action, a nontrivial normal subgroup is transitive.
An equivariant generating family then gives a cyclic quotient, so the normal
subgroup contains the derived subgroup; perfectness yields simplicity.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/PrimitiveConjugateGenerators.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for downstream calculations.
-/

@[expose] public section

namespace Atlas.GroupTheory
open MulAction

/-- A transitive normal subgroup and one member of an equivariant generating
family generate the whole group. No assumption on the orders of the generators
is required. -/
theorem normal_sup_generator_eq_top {G X : Type*} [Group G] [MulAction G X]
    (t : X → G) (ht : ∀ g x, t (g • x) = g * t x * g⁻¹)
    (hgen : Subgroup.closure (Set.range t) = ⊤) (x : X)
    (N : Subgroup G) [N.Normal] [IsPretransitive N X] :
    N ⊔ Subgroup.zpowers (t x) = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨y, rfl⟩
  obtain ⟨n, hn⟩ := exists_smul_eq N x y
  have he : t y = n.val * t x * n.val⁻¹ := by
    rw [← hn]
    exact ht n.val x
  rw [he]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left n.prop)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers (t x))))
    (Subgroup.inv_mem _ (Subgroup.mem_sup_left n.prop))

/-- In a faithful primitive action with an equivariant generating family,
every nontrivial normal subgroup contains the derived subgroup. -/
theorem commutator_le_normal_of_primitive_generators {G X : Type*}
    [Group G] [MulAction G X] [FaithfulSMul G X] [IsPreprimitive G X]
    (t : X → G) (ht : ∀ g x, t (g • x) = g * t x * g⁻¹)
    (hgen : Subgroup.closure (Set.range t) = ⊤) (x : X)
    (N : Subgroup G) [hN : N.Normal] (hne : N ≠ ⊥) : commutator G ≤ N := by
  let := normal_pretransitive (X := X) N hne
  exact hN.commutator_le_of_self_sup_commutative_eq_top
    (normal_sup_generator_eq_top t ht hgen x N) inferInstance

/-- The perfect, nontrivial case of the primitive conjugate-generator
criterion. In particular it applies to generating classes of involutions. -/
theorem simple_of_perfect_primitive_generators {G X : Type*}
    [Group G] [Nontrivial G] [Group.IsPerfect G]
    [MulAction G X] [FaithfulSMul G X] [IsPreprimitive G X]
    (t : X → G) (ht : ∀ g x, t (g • x) = g * t x * g⁻¹)
    (hgen : Subgroup.closure (Set.range t) = ⊤) (x : X) : IsSimpleGroup G := by
  constructor
  intro N hN
  by_cases hne : N = ⊥
  · exact Or.inl hne
  · have h := commutator_le_normal_of_primitive_generators t ht hgen x N hne
    rw [Group.IsPerfect.commutator_eq_top] at h
    exact Or.inr (top_unique h)

end Atlas.GroupTheory

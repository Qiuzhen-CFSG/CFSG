module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Blocks
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Projection

/-!
# Genuine local inputs for component refinement

These are the component, centralizer and block inputs used in the proof of
Aschbacher–Smith 2.3.9(7), printed pp.525–526. The Γ₀ local-structure owner
constructs them using 2.3.8 and 2.3.9(1–6). The six alternatives of 1.1.5(3)
are supplied separately, with their actual model isomorphisms and actions.
No refined classification conclusion is a field of this structure.

For centerless components we also construct the unique involution projection
from a genuine inner-action input. Its nontriviality follows from C_G(z) ≤ M
and L not contained in M, rather than from an extra assumption on the projection.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement

open Subgroup

variable {G : Type*} [Group G]

/-- The genuine local inputs common to all the model cases of 2.3.9(7).
Component subnormality is relative to H. -/
structure LocalSetup (H L M : Subgroup G) (S : Sylow 2 H) (z : G) : Prop where
  finite : Finite G
  component_le : L ≤ H
  component : Theory.GroupTheory.IsComponent H (L.subgroupOf H)
  sylow_le : (S : Subgroup H).map H.subtype ≤ M
  local_even : H ⊓ M ∈ Chapter1.He G
  overgroup_even : M ∈ Chapter1.He G
  involution : orderOf z = 2
  mem_sylow : z ∈ (S : Subgroup H).map H.subtype
  central : ∀ s ∈ (S : Subgroup H).map H.subtype, s * z = z * s
  normalizes : z ∈ normalizer (L : Set G)
  centralizer_le : centralizer ({z} : Set G) ≤ M
  moved : L = ⁅L, zpowers z⁆
  outside : ¬ L ≤ M
  blocks : LocalBlockGeneration L M ((S : Subgroup H).map H.subtype)

/-- A literal action of z on L is nontrivial in this setup. -/
theorem LocalSetup.action_ne_one {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (α : MulAut L)
    (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹) : α ≠ 1 := by
  intro he
  apply h.outside
  intro x hx
  apply h.centralizer_le
  apply mem_centralizer_singleton_iff.mpr
  have hf := hα ⟨x, hx⟩
  rw [he] at hf
  change x = z * x * z⁻¹ at hf
  exact (mul_inv_eq_iff_eq_mul.mp hf.symm).symm

/-- Squaring the actual conjugation action gives the identity. -/
theorem LocalSetup.action_sq {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (α : MulAut L)
    (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹) : α ^ 2 = 1 := by
  have hz : z ^ 2 = 1 := h.involution ▸ pow_orderOf_eq_one z
  apply MulEquiv.ext
  intro x
  rw [pow_two, MulAut.mul_apply]
  change α (α x) = x
  apply Subtype.ext
  rw [hα, hα]
  calc
    z * (z * (x : G) * z⁻¹) * z⁻¹ = (z * z) * (x : G) * (z * z)⁻¹ := by group
    _ = (x : G) := by rw [← pow_two, hz]; simp

/-- Construct the source's projection z_L from the inner action given by
1.1.5(3), in each centerless surviving model. -/
theorem LocalSetup.exists_unique_projection {H L M : Subgroup G} {S : Sylow 2 H}
    {z : G} (h : LocalSetup H L M S z) (hZ : center L = ⊥)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    ∃! t : L, IsConjugationProjection L z t ∧ orderOf t = 2 := by
  obtain ⟨t, ht, hunique⟩ := exists_unique_inner_involution hZ α
    (h.action_sq α hα) (h.action_ne_one α hα) hinner
  refine ⟨t, ⟨?_, ht.2⟩, ?_⟩
  · intro x
    rw [← hα x, ← ht.1]
    rfl
  · intro u hu
    apply hunique u
    refine ⟨?_, hu.2⟩
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change ((u * x * u⁻¹ : L) : G) = (α x : G)
    rw [hα, hu.1 x]

end CFSG.Quasithin.Chapter2.ComponentRefinement

end

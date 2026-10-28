module

public import Theory.AlgebraicGroup.Borel.RootStructure.theorem_1_12_4
public import Theory.AlgebraicGroup.Cartan.Kernels

/-!
The type `E₈` arithmetic in GLS3, Theorem 1.12.5(c)-(d), Table 1.12.5.

The standard `E₈` Cartan matrix is unimodular.  Consequently, its common
multiplicative relation kernel is trivial: applying the integral inverse of
the transposed Cartan matrix forces every coordinate to be one.  The final
transfer theorem isolates the geometric input still needed by the center
classification: any subgroup, and in particular the ambient center, that
embeds in this Cartan kernel is trivial.  This module does not use the
placeholder-backed global center theorem.
-/

namespace Theory.AlgebraicGroup

open scoped BigOperators

universe u

variable {k : Type u} [Field k]

/-- The common multiplicative kernel of the standard type-`E₈` Cartan
relations on eight coordinate units. -/
@[expose]
public def e8CartanRelationKernel : Subgroup (Fin 8 → kˣ) where
  carrier := {t | ∀ j, (∏ i, t i ^ dynkinCartanEntry ⟨.E8, 8⟩ i j) = 1}
  one_mem' := by
    intro j
    simp
  mul_mem' := by
    intro a b ha hb j
    change (∀ j, (∏ i, a i ^ dynkinCartanEntry ⟨.E8, 8⟩ i j) = 1) at ha
    change (∀ j, (∏ i, b i ^ dynkinCartanEntry ⟨.E8, 8⟩ i j) = 1) at hb
    change (∏ i, (a i * b i) ^ dynkinCartanEntry ⟨.E8, 8⟩ i j) = 1
    simp_rw [mul_zpow]
    rw [Finset.prod_mul_distrib]
    rw [ha j, hb j]
    simp
  inv_mem' := by
    intro a ha j
    change (∀ j, (∏ i, a i ^ dynkinCartanEntry ⟨.E8, 8⟩ i j) = 1) at ha
    change (∏ i, (a i)⁻¹ ^ dynkinCartanEntry ⟨.E8, 8⟩ i j) = 1
    simp_rw [inv_zpow]
    rw [Finset.prod_inv_distrib, ha j]
    simp

/-- Unimodularity of the standard `E₈` Cartan matrix makes its
multiplicative relation kernel trivial. -/
public theorem e8CartanRelationKernel_eq_bot :
    e8CartanRelationKernel (k := k) = ⊥ := by
  apply le_antisymm
  · intro t ht
    rw [Subgroup.mem_bot]
    funext i
    exact dynkinCartanRelationKernel_E8 t ht i
  · exact bot_le

/-- A subgroup admitting a faithful `E₈` Cartan-coordinate map is
trivial. -/
public theorem subgroup_eq_bot_of_injective_to_e8CartanRelationKernel
    {G : Type*} [Group G] (H : Subgroup G)
    (f : H →* e8CartanRelationKernel (k := k))
    (hf : Function.Injective f) :
    H = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_bot]
    let xH : H := ⟨x, hx⟩
    have hfx : f xH = 1 := by
      apply Subtype.ext
      apply Subgroup.mem_bot.mp
      rw [← e8CartanRelationKernel_eq_bot]
      exact (f xH).property
    have hxH : xH = 1 := hf (hfx.trans f.map_one.symm)
    exact congrArg Subtype.val hxH
  · exact bot_le

/-- The center of an algebraic group is trivial once its `E₈`
Cartan-coordinate map is faithful. -/
public theorem center_eq_bot_of_injective_to_e8CartanRelationKernel
    {K : Variety k} [AlgebraicGroup K]
    (f : Subgroup.center (Variety.Point K) →*
      e8CartanRelationKernel (k := k))
    (hf : Function.Injective f) :
    Subgroup.center (Variety.Point K) = ⊥ := by
  exact subgroup_eq_bot_of_injective_to_e8CartanRelationKernel _ f hf

end Theory.AlgebraicGroup

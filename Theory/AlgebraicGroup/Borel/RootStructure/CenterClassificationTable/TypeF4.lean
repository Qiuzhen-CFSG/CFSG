module

public import Theory.AlgebraicGroup.Cartan.Kernels
public import Theory.AlgebraicGroup.Basic

/-!
The type `F₄` arithmetic in GLS3, Table 1.12.5.

The displayed `F₄` Cartan matrix is unimodular.  Thus the common
multiplicative kernel of its four Cartan-coordinate relations is trivial;
`dynkinCartanRelationKernel_F4` supplies the integral inverse calculation.
The final geometric step is isolated as a faithful map from the ambient
center to this kernel.  `HasRootSystemType` currently provides a root-system
witness but no proved center-to-coordinate or universal-cover bridge, so this
module exposes the exact reusable transfer theorem without using the
placeholder-backed `theorem_1_12_5`.
-/

namespace Theory.AlgebraicGroup

open scoped BigOperators

universe u

variable {k : Type u} [Field k]

/-- The common multiplicative kernel of the standard type-`F₄` Cartan
relations on four coordinate units. -/
@[expose]
public def f4CartanRelationKernel : Subgroup (Fin 4 → kˣ) where
  carrier := {t | ∀ j, (∏ i, t i ^ dynkinCartanEntry ⟨.F4, 4⟩ i j) = 1}
  one_mem' := by
    intro j
    simp
  mul_mem' := by
    intro a b ha hb j
    change (∀ j, (∏ i, a i ^ dynkinCartanEntry ⟨.F4, 4⟩ i j) = 1) at ha
    change (∀ j, (∏ i, b i ^ dynkinCartanEntry ⟨.F4, 4⟩ i j) = 1) at hb
    change (∏ i, (a i * b i) ^ dynkinCartanEntry ⟨.F4, 4⟩ i j) = 1
    simp_rw [mul_zpow]
    rw [Finset.prod_mul_distrib]
    rw [ha j, hb j]
    simp
  inv_mem' := by
    intro a ha j
    change (∀ j, (∏ i, a i ^ dynkinCartanEntry ⟨.F4, 4⟩ i j) = 1) at ha
    change (∏ i, (a i)⁻¹ ^ dynkinCartanEntry ⟨.F4, 4⟩ i j) = 1
    simp_rw [inv_zpow]
    rw [Finset.prod_inv_distrib, ha j]
    simp

/-- Unimodularity of the standard `F₄` Cartan matrix makes its
multiplicative relation kernel trivial. -/
public theorem f4CartanRelationKernel_eq_bot :
    f4CartanRelationKernel (k := k) = ⊥ := by
  apply le_antisymm
  · intro t ht
    rw [Subgroup.mem_bot]
    funext i
    exact dynkinCartanRelationKernel_F4 t ht i
  · exact bot_le

/-- A subgroup admitting a faithful `F₄` Cartan-coordinate map is trivial. -/
public theorem subgroup_eq_bot_of_injective_to_f4CartanRelationKernel
    {G : Type*} [Group G] (H : Subgroup G)
    (f : H →* f4CartanRelationKernel (k := k))
    (hf : Function.Injective f) :
    H = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_bot]
    let xH : H := ⟨x, hx⟩
    have hfx : f xH = 1 := by
      apply Subtype.ext
      apply Subgroup.mem_bot.mp
      rw [← f4CartanRelationKernel_eq_bot]
      exact (f xH).property
    have hxH : xH = 1 := hf (hfx.trans f.map_one.symm)
    exact congrArg Subtype.val hxH
  · exact bot_le

/-- The algebraic-group center is trivial once its `F₄` Cartan-coordinate map
is faithful.  Constructing that map from an actual root-system witness is the
remaining geometric bridge for the source-level F4 classification leaf. -/
public theorem center_eq_bot_of_injective_to_f4CartanRelationKernel
    {K : Variety k} [AlgebraicGroup K]
    (f : Subgroup.center (Variety.Point K) →*
      f4CartanRelationKernel (k := k))
    (hf : Function.Injective f) :
    Subgroup.center (Variety.Point K) = ⊥ := by
  exact subgroup_eq_bot_of_injective_to_f4CartanRelationKernel _ f hf

end Theory.AlgebraicGroup

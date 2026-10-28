module

public import Theory.Representation.QuadraticFourGroup.CubicSections.SectionReduction.Transport
public import Theory.Representation.QuadraticFourGroup.Recognition.Overgroup

/-!
# The actual orbit in the generated overgroup

The inclusion of `E = ⟨L^B⟩` into `X = L ⊔ B` identifies its image with
the component orbit calculated inside `X`. Changing the marked component
by an element of `B` preserves this orbit. Its intrinsic two-core kills
every irreducible binary `X`-action: the orbit is normal in `X`, its core
is characteristic, and normal two-subgroups kill irreducible modules.

Source: GLS, volume 2, Theorem 25.14, Step 2. Normality is relative to `X`.
-/

@[expose] public section
open Subgroup Theory.GroupTheory

namespace Representation.QuadraticFourGroup.SectionReduction
variable {G : Type*} [Group G]

def orbitInclusion (L B : Subgroup G) : componentOrbit L B →* (L ⊔ B : Subgroup G) :=
  Subgroup.inclusion (componentOrbit_le_sup L B)

theorem localOrbit_eq_range (L B : Subgroup G) :
    componentOrbit (L.subgroupOf (L ⊔ B)) (B.subgroupOf (L ⊔ B)) =
      (orbitInclusion L B).range := by
  apply Subgroup.map_injective (L ⊔ B).subtype_injective
  rw [componentOrbit_map, map_subgroupOf_eq_of_le le_sup_left,
    map_subgroupOf_eq_of_le le_sup_right]
  change _ = (Subgroup.inclusion (componentOrbit_le_sup L B)).range.map (L ⊔ B).subtype
  rw [Subgroup.inclusion_range, map_subgroupOf_eq_of_le (componentOrbit_le_sup L B)]

theorem orbit_conjugate_component (L B : Subgroup G) (b : B) :
    componentOrbit (L.map (MulAut.conj (b : G)).toMonoidHom) B = componentOrbit L B := by
  have hB : B.map (MulAut.conj (b : G)).toMonoidHom = B :=
    mem_normalizer_iff_map_conj_eq.mp (B.le_normalizer b.property)
  have hE : (componentOrbit L B).map (MulAut.conj (b : G)).toMonoidHom =
      componentOrbit L B :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L B b.property)
  have hm := componentOrbit_map L B (MulAut.conj (b : G)).toMonoidHom
  rw [hB, hE] at hm
  exact hm.symm

variable [Finite G] {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

theorem orbit_twoCore_le_ker (L B : Subgroup G)
    (τ : Representation (ZMod 2) (L ⊔ B : Subgroup G) U) [τ.IsIrreducible] :
    pCore 2 (componentOrbit L B) ≤ (τ.comp (orbitInclusion L B)).ker := by
  let E := componentOrbit L B
  let X := L ⊔ B
  let e : E ≃* E.subgroupOf X := (subgroupOfEquivOfLe (componentOrbit_le_sup L B)).symm
  let : (E.subgroupOf X).Normal := componentOrbit_normal_subgroupOf_sup L B
  have hk := normal_twoCore_le_ker τ (E.subgroupOf X)
  intro x hx
  have he : e x ∈ pCore 2 (E.subgroupOf X) := by
    rw [← pCore_map_iso 2 e]
    exact mem_map_of_mem e.toMonoidHom hx
  exact hk he

end Representation.QuadraticFourGroup.SectionReduction

end

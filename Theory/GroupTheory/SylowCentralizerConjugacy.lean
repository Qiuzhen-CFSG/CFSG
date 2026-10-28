module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Placing a p-centralizer in a specified Sylow subgroup

If an element centralizer in a finite group is a p-group, conjugate a Sylow
subgroup containing it to the specified Sylow subgroup. The conjugate
element then has its entire centralizer in that Sylow, with the same order.
This is the Sylow-conjugacy step used in Parrott, *A characterization of
the Tits' simple group* (1972), p.674, for the two derived-core classes.
-/

namespace Subgroup

/-- The ambient image of an element centralizer inside a subgroup. -/
public theorem map_subtype_centralizer_singleton
    {G : Type*} [Group G] (H : Subgroup G) (x : H) :
    (centralizer ({x} : Set H)).map H.subtype =
      H ⊓ centralizer ({(x : G)} : Set G) := by
  ext y
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, mem_centralizer_singleton_iff.mpr
      (congrArg H.subtype (mem_centralizer_singleton_iff.mp hy))⟩
  · rintro ⟨hyH, hy⟩
    exact ⟨⟨y, hyH⟩, mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp hy)), rfl⟩

/-- A p-group element centralizer can be conjugated into any supplied Sylow
p-subgroup, preserving its cardinality. -/
public theorem exists_conj_centralizer_le_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (x : G) (hx : IsPGroup p (centralizer ({x} : Set G))) :
    ∃ a : G, centralizer ({a * x * a⁻¹} : Set G) ≤ (S : Subgroup G) ∧
      Nat.card (centralizer ({a * x * a⁻¹} : Set G)) =
        Nat.card (centralizer ({x} : Set G)) := by
  obtain ⟨P, hP⟩ := hx.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G P S
  let f := MulAut.conj a
  have hmap : (centralizer ({x} : Set G)).map f.toMonoidHom =
      centralizer ({f x} : Set G) := by
    apply le_antisymm
    · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
        map_centralizer_le_centralizer_image ({x} : Set G) f.toMonoidHom
    · intro y hy
      refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
      apply mem_centralizer_singleton_iff.mpr
      apply f.injective
      simpa only [map_mul, f.apply_symm_apply] using
        mem_centralizer_singleton_iff.mp hy
  refine ⟨a, ?_, ?_⟩
  · change centralizer ({f x} : Set G) ≤ (S : Subgroup G)
    rw [← hmap, ← ha]
    exact map_mono hP
  · change Nat.card (centralizer ({f x} : Set G)) = _
    rw [← hmap, card_map_of_injective f.injective]

end Subgroup

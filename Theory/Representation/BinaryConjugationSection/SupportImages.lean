module
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Detecting literal supports through binary section coordinates

Separated supports have disjoint coordinate images. For a support containing
the original kernel, its subspace stabilizer pulls back to the actual normalizer.
These statements retain the same coordinate map and central kernel.

Source application: Aschbacher--Smith 14.6.22--24, pp.1038--1041.
-/

public section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G E : Type*} [Group G] [AddCommGroup E] [Module (ZMod 2) E]
  {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H E}
  (c : BinaryConjugationSection H U Z ρ)

/-- Separation modulo the original kernel gives disjoint coordinate images. -/
theorem imageSpace_disjoint (A B : Subgroup G)
    (hZB : Z ≤ B) (hab : A ⊓ B ≤ Z) :
    Disjoint (c.imageSpace A) (c.imageSpace B) := by
  apply Submodule.disjoint_def.mpr
  intro v ha hb
  obtain ⟨u,hu,rfl⟩ := (c.mem_imageSpace_iff A v).mp ha
  have huB := (c.coordinates_mem_imageSpace_iff_of_kernel_le B hZB u).mp hb
  exact (c.coordinates_eq_one_iff u).mpr (hab ⟨hu,huB⟩)

/-- The coordinate stabilizer is the original support normalizer. -/
theorem subspaceStabilizer_imageSpace (A : Subgroup G) (hAU : A ≤ U) (hZA : Z ≤ A) :
    Representation.BinaryOffender.subspaceStabilizer ρ (c.imageSpace A) =
      (normalizer (A : Set G)).subgroupOf H := by
  ext x
  constructor
  · intro hx
    apply mem_normalizer_iff.mpr
    intro a
    constructor
    · intro ha
      let u : U := ⟨a,hAU ha⟩
      have hu := (c.coordinates_mem_imageSpace_iff_of_kernel_le A hZA u).mpr ha
      have hu' := (hx (c.coordinates u).toAdd).mpr hu
      rw [←c.equivariant] at hu'
      exact (c.coordinates_mem_imageSpace_iff_of_kernel_le A hZA _).mp hu'
    · intro ha
      have haU : a ∈ U := by
        have hh := (mem_normalizer_iff.mp (c.normalized x.property) a).mpr (hAU ha)
        exact hh
      let u : U := ⟨a,haU⟩
      have hu := (c.coordinates_mem_imageSpace_iff_of_kernel_le A hZA
        ⟨(x:G)*a*(x:G)⁻¹,hAU ha⟩).mpr ha
      rw [c.equivariant x u] at hu
      exact (c.coordinates_mem_imageSpace_iff_of_kernel_le A hZA u).mp
        ((hx _).mp hu)
  · intro hx v
    obtain ⟨u,rfl⟩ := c.onto (Multiplicative.ofAdd v)
    change ρ x (c.coordinates u).toAdd ∈ c.imageSpace A ↔ (c.coordinates u).toAdd ∈ c.imageSpace A
    rw [←c.equivariant,
      c.coordinates_mem_imageSpace_iff_of_kernel_le A hZA,
      c.coordinates_mem_imageSpace_iff_of_kernel_le A hZA]
    exact (mem_normalizer_iff.mp hx u).symm
end Representation.BinaryConjugationSection

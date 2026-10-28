module
public import Theory.Representation.BinaryConjugationSection
public import Theory.SpecificGroups.SL2.Affine.Action
public import Theory.Representation.SL2.BinarySmallModels

/-!
# Restricting literal conjugation coordinates to a moved subgroup

A noncentral invariant subgroup surjects onto a transitive nonzero-vector
section. Restricting the given coordinates preserves their kernel as an
intersection and keeps the original actor map. The natural SL₂ action is
transitive even after restricting scalars, so no splitting of a central
cover is needed.

Source application: Aschbacher–Smith 10.2.3(4), p.746, transporting the
chosen full-module natural section to the actual local moved subgroup.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H A B : Subgroup G}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) H V} (c : BinaryConjugationSection H A B ρ)

/-- A nonzero invariant image in a transitive section is the entire section. -/
theorem restricted_coordinates_surjective_of_transitive
    (P : Subgroup G) (hPA : P ≤ A) (hHP : H ≤ normalizer (P : Set G))
    (hPB : ¬ P ≤ B)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ h : H, ρ h v = w) :
    Function.Surjective (c.coordinates.comp (inclusion hPA)) := by
  classical
  have hex : ∃ p : P, c.coordinates (inclusion hPA p) ≠ 1 := by
    by_contra! hn
    apply hPB
    intro p hp
    exact (c.coordinates_eq_one_iff _).mp (hn ⟨p,hp⟩)
  obtain ⟨p,hp⟩ := hex
  intro v
  by_cases hv : v = 1
  · subst v
    exact ⟨1,map_one _⟩
  obtain ⟨h,hh⟩ := htrans (c.coordinates (inclusion hPA p)).toAdd v.toAdd hp hv
  let r : P := ⟨(h:G)*p*(h:G)⁻¹,(mem_normalizer_iff.mp (hHP h.property) p).mp p.property⟩
  refine ⟨r,?_⟩
  exact Multiplicative.toAdd.injective ((c.equivariant h (inclusion hPA p)).trans hh)

/-- Restrict the literal coordinates and retain the exact intersected kernel. -/
@[expose] def restrict (P : Subgroup G) (hPA : P ≤ A) (hHP : H ≤ normalizer (P : Set G))
    (honto : Function.Surjective (c.coordinates.comp (inclusion hPA))) :
    BinaryConjugationSection H P (P ⊓ B) ρ where
  section_le := hPA.trans c.section_le
  kernel_le := inf_le_left
  normalized := hHP
  coordinates := c.coordinates.comp (inclusion hPA)
  onto := honto
  kernel_eq := by
    ext p
    change c.coordinates (inclusion hPA p) = 1 ↔ (p:G) ∈ P ⊓ B
    rw [c.coordinates_eq_one_iff]
    exact ⟨fun hb => ⟨p.property,hb⟩,fun hp => hp.2⟩
  equivariant h p := c.equivariant h (inclusion hPA p)

/-- Change only the displayed kernel, leaving the coordinates definitionally unchanged. -/
@[expose] def replaceKernel (B' : Subgroup G) (hB : B = B') : BinaryConjugationSection H A B' ρ where
  section_le := c.section_le
  kernel_le := hB ▸ c.kernel_le
  normalized := c.normalized
  coordinates := c.coordinates
  onto := c.onto
  kernel_eq := c.kernel_eq.trans (congrArg (fun Z : Subgroup G => Z.subgroupOf A) hB)
  equivariant := c.equivariant

theorem restrict_coordinates (P : Subgroup G) (hPA : P ≤ A)
    (hHP : H ≤ normalizer (P : Set G))
    (honto : Function.Surjective (c.coordinates.comp (inclusion hPA))) (p : P) :
    (c.restrict P hPA hHP honto).coordinates p = c.coordinates (inclusion hPA p) := rfl

theorem replaceKernel_coordinates (B' : Subgroup G) (hB : B = B') (a : A) :
    (c.replaceKernel B' hB).coordinates a = c.coordinates a := rfl

/-- A fully moved nonzero subgroup cannot lie in a central coordinate kernel. -/
theorem not_le_kernel_of_fully_moved (P : Subgroup G)
    (hB : B ≤ centralizer (H : Set G)) (hne : P ≠ ⊥) (hm : ⁅P,H⁆ = P) :
    ¬ P ≤ B := by
  intro hp
  exact hne (hm.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr (hp.trans hB)))

open scoped MatrixGroups
variable {F : Type*} [Field F] [CharP F 2]
local instance binarySectionRestrictionFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The literal natural SL₂ coordinates remain onto every noncentral invariant subgroup. -/
theorem restricted_natural_coordinates_surjective
    (q : H →* SL(2,F)) (hq : Function.Surjective q)
    (c : BinaryConjugationSection H A B (SL2.BinarySmall.natural.comp q))
    (P : Subgroup G) (hPA : P ≤ A) (hHP : H ≤ normalizer (P : Set G))
    (hPB : ¬ P ≤ B) :
    Function.Surjective (c.coordinates.comp (inclusion hPA)) := by
  apply c.restricted_coordinates_surjective_of_transitive P hPA hHP hPB
  intro v w hv hw
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq F v w hv hw
  obtain ⟨h,rfl⟩ := hq g
  exact ⟨h,hg⟩
end Representation.BinaryConjugationSection

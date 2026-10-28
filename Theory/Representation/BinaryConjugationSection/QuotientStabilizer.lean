module
public import Theory.Representation.BinaryConjugationSection.SubspaceSection
public import Theory.Representation.BinaryOffender.IrreducibleOrbitAction

/-!
# The actual quotient actor on a lifted support

For a binary section inflated along H → D, the full subgroup preimage W
of I has actor H∩N(W). Its map to the stabilizer of I is the original
quotient map, is surjective when H → D is, and has the exact prescribed
subgroup images. Restriction of the original coordinates yields the
literal W/Z section for that actor. No replacement extension is chosen.

Source application: Aschbacher--Smith14.6.22--24, printed pp.1038--1039.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation.BinaryConjugationSection
variable {G D V : Type*} [Group G] [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {H U Z : Subgroup G} (ρ : Representation (ZMod 2) D V) (π : H →* D)
  (c : BinaryConjugationSection H U Z (ρ.comp π)) (I : Submodule (ZMod 2) V)

@[expose] def subspaceActorHom :
    (H ⊓ normalizer (c.subspacePreimage I : Set G) : Subgroup G) →*
      subspaceStabilizer ρ I where
  toFun a := ⟨π ⟨a.val,a.property.1⟩,
    (subspace_map_eq_iff ρ I _).mp
      ((c.mem_normalizer_subspacePreimage_iff I ⟨a.val,a.property.1⟩).mp a.property.2)⟩
  map_one' := Subtype.ext (map_one π)
  map_mul' a b := by
    apply Subtype.ext
    exact π.map_mul ⟨a.val,a.property.1⟩ ⟨b.val,b.property.1⟩

theorem subspaceActorHom_surjective (hπ : Function.Surjective π) :
    Function.Surjective (c.subspaceActorHom ρ π I) := by
  intro j
  obtain ⟨h,hh⟩ := hπ j.val
  have hn : h.val ∈ normalizer (c.subspacePreimage I : Set G) := by
    apply (c.mem_normalizer_subspacePreimage_iff I h).mpr
    change I.map (ρ (π h)) = I
    rw [hh]
    exact (subspace_map_eq_iff ρ I j.val).mpr j.property
  exact ⟨⟨h.val,h.property,hn⟩,Subtype.ext hh⟩

theorem subspaceActorHom_image (K : Subgroup G) :
    (K.subgroupOf (H ⊓ normalizer (c.subspacePreimage I : Set G))).map
        (c.subspaceActorHom ρ π I) =
      ((K.subgroupOf H).map π).subgroupOf (subspaceStabilizer ρ I) := by
  ext j
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact ⟨⟨k.val,k.property.1⟩,hk,rfl⟩
  · rintro ⟨k,hk,hkj⟩
    have hn : k.val ∈ normalizer (c.subspacePreimage I : Set G) := by
      apply (c.mem_normalizer_subspacePreimage_iff I k).mpr
      change I.map (ρ (π k)) = I
      rw [hkj]
      exact (subspace_map_eq_iff ρ I j.val).mpr j.property
    exact ⟨⟨k.val,k.property,hn⟩,hk,Subtype.ext hkj⟩

/-- Coordinates on W/Z equivariant for the full original stabilizer and
its actual quotient image. -/
theorem exists_subspaceActorSection :
    ∃ d : BinaryConjugationSection
        (H ⊓ normalizer (c.subspacePreimage I : Set G)) (c.subspacePreimage I) Z
        ((stabilizerRepresentation ρ I).comp (c.subspaceActorHom ρ π I)),
      ∀ w : c.subspacePreimage I, (d.coordinates w).toAdd.val =
        (c.coordinates ⟨w,c.subspacePreimage_le I w.property⟩).toAdd := by
  let A := H ⊓ normalizer (c.subspacePreimage I : Set G)
  have hi : A.subgroupOf H ≤ subspaceStabilizer (ρ.comp π) I := by
    intro a ha
    exact (subspace_map_eq_iff _ I a).mp ((c.mem_normalizer_subspacePreimage_iff I a).mp ha.2)
  have hWA : c.subspacePreimage I ≤ A :=
    le_inf ((c.subspacePreimage_le I).trans c.section_le) (c.subspacePreimage I).le_normalizer
  let d := c.subspaceSection A (show A ≤ H from inf_le_left) I hi hWA
  have he : subspaceAction A (show A ≤ H from inf_le_left) I hi =
      (stabilizerRepresentation ρ I).comp (c.subspaceActorHom ρ π I) := rfl
  refine ⟨he ▸ d, ?_⟩
  intro w
  change (d.coordinates w).toAdd.val = _
  exact c.subspaceSection_coordinates A (show A ≤ H from inf_le_left) I hi hWA w

end Representation.BinaryConjugationSection

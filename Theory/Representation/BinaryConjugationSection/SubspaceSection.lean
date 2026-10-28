module
public import Theory.Representation.BinaryConjugationSection.SubspacePreimages

/-!
# Coordinates on a lifted component subspace

Restrict the original coordinate map to the full preimage of an invariant
subspace. If that preimage lies in its actor, it is a binary conjugation
section for the original actor and the same kernel. Its coordinates agree
pointwise with the original coordinates, and its action is the original
restricted representation, relabeled by the literal subgroup inclusion.

This supplies the actual W/Z cover behind the hatted natural marking in
Aschbacher--Smith 14.6.22, printed p.1038.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation.BinaryConjugationSection
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H V}
  (c : BinaryConjugationSection H U Z ρ)

/-- The original subgroup action on the prescribed invariant subspace. -/
@[expose] def subspaceAction (K : Subgroup G) (hKH : K ≤ H)
    (I : Submodule (ZMod 2) V) (hi : K.subgroupOf H ≤ subspaceStabilizer ρ I) :
    Representation (ZMod 2) K I :=
  (invariantSubspace ρ (K.subgroupOf H) I hi).toRepresentation.comp
    (subgroupOfEquivOfLe hKH).symm.toMonoidHom

/-- Restrict the original coordinates to the full subspace preimage. -/
def subspaceSection (K : Subgroup G) (hKH : K ≤ H)
    (I : Submodule (ZMod 2) V) (hi : K.subgroupOf H ≤ subspaceStabilizer ρ I)
    (hWK : c.subspacePreimage I ≤ K) :
    BinaryConjugationSection K (c.subspacePreimage I) Z (subspaceAction K hKH I hi) where
  section_le := hWK
  kernel_le := c.kernel_le_subspacePreimage I
  normalized := c.subspacePreimage_normalized K hKH I hi
  coordinates := {
    toFun := fun w => Multiplicative.ofAdd
      ⟨(c.coordinates ⟨w,c.subspacePreimage_le I w.property⟩).toAdd,
        ((c.mem_subspacePreimage I w).mp w.property).choose_spec⟩
    map_one' := by apply Subtype.ext; exact congrArg Multiplicative.toAdd (map_one c.coordinates)
    map_mul' := by
      intro w v
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd (map_mul c.coordinates
        ⟨w,c.subspacePreimage_le I w.property⟩ ⟨v,c.subspacePreimage_le I v.property⟩) }
  onto := by
    intro i
    obtain ⟨u,hu⟩ := c.onto (Multiplicative.ofAdd i.toAdd.val)
    have hw : (u : G) ∈ c.subspacePreimage I :=
      (c.mem_subspacePreimage I u).mpr ⟨u.property,hu.symm ▸ i.toAdd.property⟩
    exact ⟨⟨u,hw⟩,Subtype.ext (congrArg Multiplicative.toAdd hu)⟩
  kernel_eq := by
    ext w
    change (⟨(c.coordinates ⟨w,c.subspacePreimage_le I w.property⟩).toAdd,_⟩ : I) = 0 ↔
      (w : G) ∈ Z
    rw [Subtype.ext_iff]
    exact c.coordinates_eq_one_iff _
  equivariant k w := by
    apply Subtype.ext
    exact c.equivariant ⟨k,hKH k.property⟩ ⟨w,c.subspacePreimage_le I w.property⟩

/-- The restricted coordinates are literally the original coordinates. -/
theorem subspaceSection_coordinates (K : Subgroup G) (hKH : K ≤ H)
    (I : Submodule (ZMod 2) V) (hi : K.subgroupOf H ≤ subspaceStabilizer ρ I)
    (hWK : c.subspacePreimage I ≤ K) (w : c.subspacePreimage I) :
    ((c.subspaceSection K hKH I hi hWK).coordinates w).toAdd.val =
      (c.coordinates ⟨w,c.subspacePreimage_le I w.property⟩).toAdd := by
  rfl

end Representation.BinaryConjugationSection

module

public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Extending an FF action to the full linear normalizer

If L is normal in H, the image of any representation of H normalizes the
image of L. The inclusion of the former image in this full linear normalizer
is injective and leaves every vector action unchanged. Transporting an
offender along it proves the FF property for the full normalizer.

This is the passage from the action image in B.1.11 to the normalizer used
in B.1.13 of Aschbacher–Smith, *The Classification of Quasithin Groups*,
printed p. 73. It requires only relative normality in H, not faithfulness
of H or an identification of H with the full normalizer.
-/

@[expose] public section
namespace Representation.BinaryOffender
open Subgroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The full group of invertible linear maps normalizing the actual action image. -/
def linearNormalizer : Subgroup (Module.End (ZMod 2) V)ˣ :=
  normalizer (actionImage ρ : Set (Module.End (ZMod 2) V)ˣ)

/-- The tautological action of the full linear normalizer on the same vector space. -/
def normalizerRepresentation : Representation (ZMod 2) (linearNormalizer ρ) V :=
  (Units.coeHom _).comp (linearNormalizer ρ).subtype

/-- Relative normality places the larger action image in the full normalizer. -/
theorem actionImage_le_linearNormalizer (L : Subgroup G) [L.Normal] :
    actionImage ρ ≤ linearNormalizer (ρ.comp L.subtype) := by
  have he : actionImage (ρ.comp L.subtype) = L.map ρ.asGroupHom := by
    ext x
    simp only [actionImage, MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨l, l.property, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, rfl⟩
  change actionImage ρ ≤ normalizer (actionImage (ρ.comp L.subtype) : Set _)
  rw [he]
  rintro x ⟨g, rfl⟩
  exact L.le_normalizer_map ρ.asGroupHom
    (mem_map_of_mem _ (show g ∈ normalizer (L : Set G) from
      le_normalizer_of_normal (mem_top g)))

/-- The same offender, embedded injectively, witnesses FF for the full normalizer. -/
theorem isFFModule_linearNormalizer (L : Subgroup G) [L.Normal]
    (h : IsFFModule (imageRepresentation ρ)) :
    IsFFModule (normalizerRepresentation (ρ.comp L.subtype)) := by
  exact h.map_equivariant _ _
    (inclusion (actionImage_le_linearNormalizer ρ L)) (inclusion_injective _)
    (LinearEquiv.refl _ _) (fun _ _ => rfl)

/-- The version with a marked homomorphism, retaining the original domain of
the smaller action. Only its image is required to be normal. -/
theorem isFFModule_linearNormalizer_of_normal_range
    {L : Type*} [Group L] (ι : L →* G) [ι.range.Normal]
    (h : IsFFModule (imageRepresentation ρ)) :
    IsFFModule (normalizerRepresentation (ρ.comp ι)) := by
  have he : actionImage (ρ.comp ι) = actionImage (ρ.comp ι.range.subtype) := by
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨⟨ι l, ⟨l, rfl⟩⟩, Units.ext rfl⟩
    · rintro ⟨⟨_, l, rfl⟩, rfl⟩
      exact ⟨l, Units.ext rfl⟩
  have hh := isFFModule_linearNormalizer ρ ι.range h
  unfold normalizerRepresentation linearNormalizer at hh ⊢
  rwa [he]

end Representation.BinaryOffender

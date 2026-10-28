module

public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Representation.BinaryIrreducibleCentralizer
public import Theory.Representation.Quotient

/-!
# Faithful images and elementary actors in the full linear normalizer

Passing to the faithful action image leaves the full linear normalizer and
its tautological action unchanged. Irreducibility passes to that image.
Every elementary abelian two-subgroup of the normalizer embeds in the
image's automorphism group: its conjugation kernel consists of centralizing
involutions, which the binary Schur argument kills.

This supplies the faithful-image and scalar-kernel reductions in the
full-normalizer application of Aschbacher–Smith B.1.13, printed p.73.
No assertion about the generalized Fitting subgroup of the normalizer,
or about an offender lying in the action image, is needed.
-/

@[expose] public section
namespace Representation.BinaryOffender
open Subgroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Taking the tautological action of the image produces the same subgroup
of the invertible binary linear maps. -/
theorem actionImage_imageRepresentation :
    actionImage (imageRepresentation ρ) = actionImage ρ := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact x.property
  · intro hg
    exact ⟨⟨g, hg⟩, Units.ext rfl⟩

/-- The literal full normalizer is unchanged by passage to the action image. -/
theorem linearNormalizer_imageRepresentation :
    linearNormalizer (imageRepresentation ρ) = linearNormalizer ρ := by
  unfold linearNormalizer
  rw [actionImage_imageRepresentation]

/-- Consequently the FF property is preserved for the full normalizer action. -/
theorem isFFModule_normalizer_imageRepresentation_iff :
    IsFFModule (normalizerRepresentation (imageRepresentation ρ)) ↔
      IsFFModule (normalizerRepresentation ρ) := by
  unfold normalizerRepresentation
  rw [linearNormalizer_imageRepresentation]

/-- Irreducibility is preserved on the same module by the actual action image. -/
theorem imageRepresentation_isIrreducible (hi : IsIrreducible ρ) :
    IsIrreducible (imageRepresentation ρ) :=
  (irreducible_comp_surjective_iff (actionHom ρ)
    ρ.asGroupHom.rangeRestrict_surjective (imageRepresentation ρ)).mp hi

/-- The full normalizer's tautological representation is faithful. -/
theorem normalizerRepresentation_injective :
    Function.Injective (normalizerRepresentation ρ) := by
  intro g h he
  exact Subtype.ext (Units.ext he)

/-- An elementary two-subgroup of the full normalizer acts faithfully by
conjugation on the original action image, even when ρ itself has a kernel. -/
theorem normalizer_elementary_conjugation_injective (hi : IsIrreducible ρ)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A] :
    Function.Injective ((actionImage ρ).normalizerMonoidHom.comp A.subtype) := by
  let : IsIrreducible ((Units.coeHom (Module.End (ZMod 2) V)).comp
      (actionImage ρ).subtype) := imageRepresentation_isIrreducible ρ hi
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro a ha
  apply Subtype.ext
  apply Subtype.ext
  apply BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
    (Units.coeHom (Module.End (ZMod 2) V)) (actionImage ρ)
    (fun _ _ h => Units.ext h)
  · exact congrArg (fun a : linearNormalizer ρ => a.val)
      (elemPow_eq_one_of_isElementaryAbelian (a : linearNormalizer ρ) a.property)
  · change (a : linearNormalizer ρ) ∈ (actionImage ρ).normalizerMonoidHom.ker at ha
    rw [normalizerMonoidHom_ker] at ha
    exact ha

/-- The actual FF witness survives scalar-kernel removal, with its original
fixed-space codimension and a faithful conjugation action on the image. -/
theorem exists_offender_with_injective_conjugation (hi : IsIrreducible ρ)
    (hff : IsFFModule (normalizerRepresentation ρ)) :
    ∃ A : Subgroup (linearNormalizer ρ),
      IsOffender (normalizerRepresentation ρ) A ∧
      Function.Injective ((actionImage ρ).normalizerMonoidHom.comp A.subtype) := by
  obtain ⟨A, hA⟩ := hff
  let := hA.1.2
  exact ⟨A, hA, normalizer_elementary_conjugation_injective ρ hi A⟩

end Representation.BinaryOffender

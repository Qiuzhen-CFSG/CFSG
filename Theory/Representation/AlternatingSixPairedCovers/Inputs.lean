module
public import Theory.Representation.BinaryPermutationSixCover
public import Theory.Representation.BinaryAlternatingSixModels
public import Theory.Representation.BinaryOffender.Defs

/-!
# Marked paired natural modules and their covers

This shared input retains the literal alternating component and the two
covering subspaces in a binary representation. Each support has an actual
intertwining equivalence with the natural four-space or the five-dimensional
augmentation core; the companion uses the explicit exceptional automorphism.
The ambient actor may interchange the supports. Their intersection and their
intersection with the fixed space are unrestricted.

These are model inputs for the remaining calculation in Aschbacher--Smith,
14.6.24(2), printed p. 1041, extracted from 14.6.20--23. The structure itself
asserts neither that the source supplies these inputs nor any quadratic-actor
classification. Its source consumer is `AlternatingSix.Application`.
-/

@[expose] public section
open Subgroup Representation
namespace AlternatingSixPairedCovers

variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]

/-- Concrete paired supports for the alternating-six calculation. The component
is embedded and self-centralizing in the actor. The two supports have actual
natural-or-augmentation-core coordinates, with the second marking twisted by
the specified exceptional automorphism. Their sum, together with the fixed
space, spans the ambient module. No directness or fixed-free assertion is a
field, and the full actor is allowed to interchange the supports. -/
structure Data (ρ : Representation (ZMod 2) H E) where
  component : alternatingGroup (Fin 6) →* H
  injective : Function.Injective component
  normal : component.range.Normal
  centralizer : Subgroup.centralizer (component.range : Set H) = ⊥
  first : Subrepresentation (ρ.comp component)
  second : Subrepresentation (ρ.comp component)
  first_model : BinaryPermutation.SixCover.IsNaturalOrCore first.toRepresentation
    (alternatingGroup (Fin 6)).subtype
  second_model : BinaryPermutation.SixCover.IsNaturalOrCore second.toRepresentation
    (BinaryAlternatingSix.diagramAut.toMonoidHom.comp (alternatingGroup (Fin 6)).subtype)
  span : first.toSubmodule ⊔ second.toSubmodule ⊔ BinaryOffender.fixedSpace ρ ⊤ = ⊤
  permutes : ∀ h : H,
    ((∀ v ∈ first, ρ h v ∈ first) ∧ (∀ v ∈ second, ρ h v ∈ second)) ∨
    ((∀ v ∈ first, ρ h v ∈ second) ∧ (∀ v ∈ second, ρ h v ∈ first))

end AlternatingSixPairedCovers

module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Generators
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.ImageWords
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageData.Points
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.GeneratorActions.Seeds

/-!
# Assembly of the eight exact coordinate actions

The proposed image tables give a common interface for two independent finite
certificates: evaluation of the shared Fi22 words, and evaluation of the Fi23
witnesses on the published coordinates. The theorem below combines those
certificates using the literal `ImageWords.image`, `witnessGenerator`, and
`ImageData.point`; it retains the extra `none` coordinate.

Both certificate families remain explicit premises until their numerical
proofs have been completed. The seed word calculations alone do not establish
the eight actions. This module neither identifies nor exhausts a centralizer.
The consumer is `imageContainment_of_word_actions` in `ImageContainment.lean`.

Source: GLS3 Table 5.3u and the Fischer-group discussion near line 1042 of
`refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate

/-- Exact assembly contract for the two independent numerical certificates.
This is conditional; the unconditional eight-action theorem needs both inputs. -/
theorem witnessGenerator_point_action_of_tables
    (hwords : ∀ (j : Fin 8) (x : Fin 3510),
      (ImageWords.image j).val x = GeneratorActions.imageAction j x)
    (hwitnesses : ∀ (j : Fin 8) (i : Option (Fin 3510)),
      witnessGenerator j (ImageData.point i) =
        ImageData.point (Option.map (GeneratorActions.imageAction j) i)) :
    ∀ (j : Fin 8) (i : Option (Fin 3510)),
      witnessGenerator j (ImageData.point i) =
        ImageData.point (Option.map (ImageWords.image j).val i) := by
  intro j i
  cases i with
  | none => exact hwitnesses j none
  | some x =>
    simpa only [Option.map_some, hwords j x] using hwitnesses j (some x)

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate

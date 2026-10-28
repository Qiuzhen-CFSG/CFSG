module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.FixedPointSetup
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageData.Points
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Generators
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.ImageWords
public import Theory.GroupAction.PermutationLiftSubgroup
public import Theory.GroupAction.PermutationImageComparison

/-!
# Assembling full-centralizer image containment from concrete certificates

The permutations inducing an element of the exact Fi22 group on the published
coordinates form a subgroup. Hence eight checked generator actions extend to
the entire explicit witness group. A separate exhaustion proof must put every
element of the actual Fi23 centralizer in that group. This module proves that
assembly step, retaining both unfinished certificate obligations explicitly.
It does not assert unconditional containment or centralizer identification.

The `none` coordinate is included throughout, so fixation of the extra letter
15181 cannot be dropped. No fixed-set coverage or kernel-rigidity hypothesis is
used. The image equivalence is assembled by the independent `Image` consumer.

Source: GLS3 Table 5.3u, including the conjugation action around line 754, and
the Fischer paragraph around line 1042 of
`refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

@[expose] public section

namespace Sporadic.Fischer.Fi23.CentralizerSection

open Theory.GroupAction Theory.GroupAction.PermutationImageComparison
open ImageContainmentCertificate

/-- The exact Fi22 permutation group on the 3510 coordinates, with an extra
fixed coordinate. -/
def coordinateGroup : Subgroup (Equiv.Perm (Option (Fin 3510))) :=
  Fi22.generated.map (withFixedPoint (Equiv.refl _))

theorem witnessGroup_le_coordinateLift
    (hgenerators : ∀ j : Fin 8, ∃ p : Equiv.Perm (Fin 3510),
      p ∈ Fi22.generated ∧ ∀ i : Option (Fin 3510),
        witnessGenerator j (ImageData.point i) = ImageData.point (Option.map p i)) :
    witnessGroup ≤ permutationLiftSubgroup ImageData.point coordinateGroup := by
  apply closure_le_permutationLiftSubgroup
  rintro _ ⟨j, rfl⟩
  obtain ⟨p, hp, he⟩ := hgenerators j
  refine ⟨withFixedPoint (Equiv.refl _) p, ⟨p, hp, rfl⟩, ?_⟩
  exact he

/-- The actual consumer of centralizer exhaustion and the eight coordinate
certificates. Both premises still require independent concrete proofs. -/
theorem imageContainment_of_witness_certificates
    (hcoverage : ∀ g : numerator, inclusion g.val ∈ witnessGroup)
    (hgenerators : ∀ j : Fin 8, ∃ p : Equiv.Perm (Fin 3510),
      p ∈ Fi22.generated ∧ ∀ i : Option (Fin 3510),
        witnessGenerator j (ImageData.point i) = ImageData.point (Option.map p i)) :
    ∀ g : numerator, ∃ p : Equiv.Perm (Fin 3510), p ∈ Fi22.generated ∧
      ∀ i : Option (Fin 3510),
        inclusion g.val (ImageData.point i) = ImageData.point (Option.map p i) := by
  intro g
  obtain ⟨q, hq, he⟩ := witnessGroup_le_coordinateLift hgenerators (hcoverage g)
  obtain ⟨p, hp, rfl⟩ := hq
  refine ⟨p, hp, ?_⟩
  exact he

/-- The explicit Fi22 words discharge all image-membership obligations. What
remains is centralizer coverage and eight pointwise permutation identities. -/
theorem imageContainment_of_word_actions
    (hcoverage : ∀ g : numerator, inclusion g.val ∈ witnessGroup)
    (hactions : ∀ (j : Fin 8) (i : Option (Fin 3510)),
      witnessGenerator j (ImageData.point i) =
        ImageData.point (Option.map (ImageWords.image j).val i)) :
    ∀ g : numerator, ∃ p : Equiv.Perm (Fin 3510), p ∈ Fi22.generated ∧
      ∀ i : Option (Fin 3510),
        inclusion g.val (ImageData.point i) = ImageData.point (Option.map p i) := by
  apply imageContainment_of_witness_certificates hcoverage
  intro j
  exact ⟨(ImageWords.image j).val, (ImageWords.image j).property, hactions j⟩

end Sporadic.Fischer.Fi23.CentralizerSection

module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Elementary
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.DoubleCosets.Checks

/-!
# The 150 double cosets cover the auxiliary HS point stabilizer

The finite certificate gives 5760 distinct products `a * representative i * b`
for each of three prescribed images of letter 1. Left multiplication by the
normalizer words moves these three images to 55, 11, and 11 distinct letters.
Consequently the translated rows give an injection of `Fin 77 × Fin 5760`
into `CertifiedStabilizer`. Its previously certified order is 443520, so the
injection is surjective. Both factors remain in `normalizerCandidate`.

The word definitions are the exact shared definitions in `CertificateData`.
Every computational assertion is kernel checked in the descendant modules.
Neither full normalizer equality nor an actual-carrier comparison is needed.
Source context: GLS3 Table 5.3m, printed p.274, and Aschbacher–Smith p.510.
The retained ATLAS witnesses and original generator are documented in
`DoubleCosets/source/README.md`.
-/

namespace Sporadic.LeechRelated.HS.SmallIndex.DoubleCosetCertificate

private theorem normalWord_mem (i : Fin 55) : normalWord i ∈ normalizerCandidate := by
  apply normalizerCandidate.mul_mem
  · exact normalizerCandidate.pow_mem
      (show elevenElement ∈ normalizerCandidate from
        Subgroup.mem_sup_left (Subgroup.mem_zpowers elevenElement)) _
  · exact normalizerCandidate.pow_mem
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers normalizerElement)) _

private theorem rowMap_eq (k : Fin 3) (i : Fin 5760) (x : Fin 100) :
    rowMap k i x = (rowElement k i : Equiv.Perm (Fin 100)) x := by
  simp only [rowMap, normalMap_eq, representativeMap_eq]
  rfl

private theorem rowElement_injective (k : Fin 3) : Function.Injective (rowElement k) := by
  intro i j h
  apply (rowKey_strictMono k).injective
  change key (rowMap k i) = key (rowMap k j)
  have hi : rowMap k i = (rowElement k i : Equiv.Perm (Fin 100)) := funext (rowMap_eq k i)
  have hj : rowMap k j = (rowElement k j : Equiv.Perm (Fin 100)) := funext (rowMap_eq k j)
  rw [hi, hj, h]

/-- Translate each slice to all of its 55 or 11 distinct point images. -/
private def translated (i : Fin 77 × Fin 5760) : CertifiedStabilizer :=
  normalWord (orbitFactor i.1) * rowElement (orbitSlice i.1) i.2

private theorem translated_point (j : Fin 77) (i : Fin 5760) :
    (translated (j, i) : Equiv.Perm (Fin 100)) 1 = orbitPoint j := by
  change (normalWord (orbitFactor j) : Equiv.Perm (Fin 100))
    ((rowElement (orbitSlice j) i : Equiv.Perm (Fin 100)) 1) = _
  rw [← rowMap_eq, rowMap_pivot, ← normalMap_eq]
  rfl

private theorem translated_injective : Function.Injective translated := by
  rintro ⟨j, i⟩ ⟨j', i'⟩ h
  have hp := congrArg (fun g : CertifiedStabilizer => (g : Equiv.Perm (Fin 100)) 1) h
  rw [translated_point, translated_point] at hp
  have hj := orbitPoint_injective hp
  subst j'
  have hi : rowElement (orbitSlice j) i = rowElement (orbitSlice j) i' :=
    mul_left_cancel h
  have he := rowElement_injective (orbitSlice j) hi
  subst i'
  rfl

private theorem translated_surjective : Function.Surjective translated := by
  apply (translated_injective.bijective_of_nat_card_le ?_).2
  rw [certifiedStabilizer_card, Nat.card_prod, Nat.card_fin, Nat.card_fin]

end Sporadic.LeechRelated.HS.SmallIndex.DoubleCosetCertificate

namespace Sporadic.LeechRelated.HS.SmallIndex
open DoubleCosetCertificate

/-- The 150 published double cosets cover the auxiliary HS point stabilizer. -/
public theorem normalizerCandidate_doubleCosetCover (g : CertifiedStabilizer) :
    ∃ i : Fin 150, ∃ a b : CertifiedStabilizer,
      a ∈ normalizerCandidate ∧ b ∈ normalizerCandidate ∧
      g = a * representative i * b := by
  obtain ⟨⟨j, k⟩, h⟩ := translated_surjective g
  refine ⟨rowRepresentative (orbitSlice j) k,
    normalWord (orbitFactor j) * normalWord (rowLeft (orbitSlice j) k),
    normalWord (rowRight (orbitSlice j) k),
    normalizerCandidate.mul_mem (normalWord_mem _) (normalWord_mem _),
    normalWord_mem _, ?_⟩
  simpa only [translated, rowElement, mul_assoc] using h.symm

end Sporadic.LeechRelated.HS.SmallIndex

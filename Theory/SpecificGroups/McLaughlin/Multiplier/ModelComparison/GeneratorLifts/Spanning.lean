module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.SourceMembership
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechFullIsometries
/-!
# Connecting the finite coordinate table to Leech generation

The table consists of the odd glue, twelve doubled Golay generators,
23 coordinate differences, and one axis vector. The existing Leech generating
criterion therefore applies to this exact table. Taking the inverse image of
the rational lattice gives preservation from the finite image certificates.
The generating criterion is the attributed ATLAS port imported above.
-/
@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
open Atlas.Codes Atlas.Lattices Atlas.Conway
open scoped Matrix BigOperators

theorem leech_le_of_sourceVectors (P : Submodule ℤ IntegerCoordinates)
    (h : ∀ j, vectorOfData (sourceVectors j) ∈ P) : leech ≤ P := by
  apply leech_le_of_generators P (coordinate 0)
  · intro i
    have hi : i = coordinate (coordinateIndex i) := (coordinateIndex_apply i).symm
    rw [hi]
    by_cases hz : coordinateIndex i = 0
    · simp only [hz, sub_self]; exact P.zero_mem
    · have he : ∀ j : Fin 23,
          coordinateVector (coordinate j.succ) 4 - coordinateVector (coordinate 0) 4 =
          vectorOfData (sourceVectors ⟨j.val + 13, by omega⟩) := by decide +kernel
      have hs : coordinateIndex i = (⟨(coordinateIndex i).val - 1, by omega⟩ : Fin 23).succ := by
        apply Fin.ext; simp; omega
      rw [hs, he]
      exact h _
  · have he : coordinateVector (coordinate 0) 8 = vectorOfData (sourceVectors 36) := by
      decide +kernel
    rw [he]; exact h _
  · intro j
    have he : ∀ j : Fin 12, (2 : ℤ) • golayIntegerLift (golayGenerators j) =
        vectorOfData (sourceVectors ⟨j.val + 1, by omega⟩) := by decide +kernel
    rw [he]; exact h _
  · have he : oddGlue (coordinate 0) = vectorOfData (sourceVectors 0) := by decide +kernel
    rw [he]; exact h _

theorem rationalLeech_preserved_of_sourceVectors
    (g : RationalCoordinates ≃ₗ[ℚ] RationalCoordinates)
    (h : ∀ j, g (rationalEmbedding (vectorOfData (sourceVectors j))) ∈ rationalLeech)
    {x : RationalCoordinates} (hx : x ∈ rationalLeech) : g x ∈ rationalLeech := by
  rcases hx with ⟨v,hv,rfl⟩
  exact leech_le_of_sourceVectors
    (rationalLeech.comap ((g.restrictScalars ℤ).toLinearMap.comp rationalEmbedding)) h hv

end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison

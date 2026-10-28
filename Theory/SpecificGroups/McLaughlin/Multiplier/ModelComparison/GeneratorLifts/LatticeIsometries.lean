module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.Spanning
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.Orthogonal
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.ImageAMembership
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.ImageAInvMembership
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.ImageBMembership
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.ImageBInvMembership
/-!
# The matrices are elements of the actual marked Leech stabilizer

Finite forward and inverse image certificates and the Leech generation
criterion give preservation of the whole lattice. Orthogonality permits
restriction to an integral isometry; fixation of the two specified vectors
then places it in the actual pointwise triangle stabilizer.
-/
@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
open Atlas.Codes Atlas.Lattices Atlas.Conway

theorem mapA_preserves_lattice (x : RationalCoordinates) :
    x ∈ rationalLeech ↔ mapA x ∈ rationalLeech := by
  have hf := rationalLeech_preserved_of_sourceVectors (x := x) mapA (fun j => by
    rw [mapA_source]; exact ⟨_, imageAVectors_mem j, rfl⟩)
  have hi := rationalLeech_preserved_of_sourceVectors (x := mapA x) mapA.symm (fun j => by
    rw [mapA_inverse_source]; exact ⟨_, imageAInvVectors_mem j, rfl⟩)
  exact ⟨hf, fun hx => by simpa using hi hx⟩

theorem mapB_preserves_lattice (x : RationalCoordinates) :
    x ∈ rationalLeech ↔ mapB x ∈ rationalLeech := by
  have hf := rationalLeech_preserved_of_sourceVectors (x := x) mapB (fun j => by
    rw [mapB_source]; exact ⟨_, imageBVectors_mem j, rfl⟩)
  have hi := rationalLeech_preserved_of_sourceVectors (x := mapB x) mapB.symm (fun j => by
    rw [mapB_inverse_source]; exact ⟨_, imageBInvVectors_mem j, rfl⟩)
  exact ⟨hf, fun hx => by simpa using hi hx⟩

def rationalIsometryA : rationalLatticeIsometries :=
  ⟨mapA, mapA_form, mapA_preserves_lattice⟩
def rationalIsometryB : rationalLatticeIsometries :=
  ⟨mapB, mapB_form, mapB_preserves_lattice⟩

theorem mapA_fixes_vector :
    mapA (rationalEmbedding (normSixVector co3MarkedCoordinate).val) =
      rationalEmbedding (normSixVector co3MarkedCoordinate).val := by decide +kernel

theorem mapB_fixes_vector :
    mapB (rationalEmbedding (normSixVector co3MarkedCoordinate).val) =
      rationalEmbedding (normSixVector co3MarkedCoordinate).val := by decide +kernel

theorem mapA_fixes_endpoint : mapA (rationalEmbedding mclEndpoint.val) =
    rationalEmbedding mclEndpoint.val := by decide +kernel

theorem mapB_fixes_endpoint : mapB (rationalEmbedding mclEndpoint.val) =
    rationalEmbedding mclEndpoint.val := by decide +kernel

def markedLiftA : Atlas.Sporadic.McLaughlin.Model :=
  ⟨⟨restrictionIsometry rationalIsometryA, by
      change (restrictToLeech rationalIsometryA) (normSixVector co3MarkedCoordinate) = _
      apply Subtype.ext
      apply rationalEmbedding_injective
      rw [restriction_agrees]
      exact mapA_fixes_vector⟩, by
    change (restrictToLeech rationalIsometryA) mclEndpoint = _
    apply Subtype.ext
    apply rationalEmbedding_injective
    rw [restriction_agrees]
    exact mapA_fixes_endpoint⟩

def markedLiftB : Atlas.Sporadic.McLaughlin.Model :=
  ⟨⟨restrictionIsometry rationalIsometryB, by
      change (restrictToLeech rationalIsometryB) (normSixVector co3MarkedCoordinate) = _
      apply Subtype.ext
      apply rationalEmbedding_injective
      rw [restriction_agrees]
      exact mapB_fixes_vector⟩, by
    change (restrictToLeech rationalIsometryB) mclEndpoint = _
    apply Subtype.ext
    apply rationalEmbedding_injective
    rw [restriction_agrees]
    exact mapB_fixes_endpoint⟩
end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison

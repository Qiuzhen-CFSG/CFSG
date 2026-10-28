module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.Words
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates.Transfer
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates.CoordinateEmbedding
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates.MatrixRelations

/-!
# Assembly of the local eleven certificates

The coordinate group and its two cyclic orbits are kernel-certified in the
child modules. The following transfer theorems isolate the remaining work:
construct the faithful coordinate realization from the eleven-group relations,
and certify those relations and the six normalizer identities for the concrete
ATLAS words. Once these inputs are constructed, the two conclusions here are
exactly the local inputs required by `Elevens.coverage_of_local_certificates`.

Source of the concrete words: ATLAS J4G1-max7W1, documented in `Elevens.Words`.
-/

public section
namespace Janko4.Simplicity.Elevens
open LocalCoordinates

/-- A faithful coordinate realization certifies the order of the proposed
Sylow eleven subgroup. The realization remains an explicit certificate input. -/
theorem local_card_of_coordinate_embedding
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (f : Coord →* Model) (hf : Function.Injective f)
    (hX : f X = localX (a hA) (b hB))
    (hY : f Y = localY (a hA) (b hB))
    (hZ : f Z = localZ (a hA) (b hB)) :
    Nat.card (localSubgroup hA hB) = 1331 := by
  exact coordinate_card f hf _ _ _ hX hY hZ rfl

/-- Realizing the coordinate actions as conjugations certifies local cyclic
coverage. Both the realization and the normalizer identities are explicit inputs. -/
theorem local_coverage_of_coordinate_embedding
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (f : Coord →* Model)
    (hX : f X = localX (a hA) (b hB))
    (hY : f Y = localY (a hA) (b hB))
    (hZ : f Z = localZ (a hA) (b hB))
    (hn : ElevenNormalizerRelations
      (normalizerWords (a hA) (b hB)).1 (normalizerWords (a hA) (b hB)).2
      (localX (a hA) (b hB)) (localY (a hA) (b hB)) (localZ (a hA) (b hB))) :
    ∀ w : Model, w ∈ localSubgroup hA hB → orderOf w = 11 →
      ∃ (j : Fin 2) (n : ℕ) (g : Model),
        localRepresentative (a hA) (b hB) j = g * w ^ n * g⁻¹ := by
  intro w hw ho
  have hw1 : w ≠ 1 := by
    intro h
    simp only [h, orderOf_one] at ho
    norm_num at ho
  exact coordinate_coverage f _ _ _ _ _ hX hY hZ rfl hn w hw hw1

/- The two concrete certificates are obtained by combining the kernel-checked
   matrix relations with the faithful realization of the coordinate group. -/

/-- The concrete words generate a subgroup of order `11^3`. -/
theorem local_card (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    Nat.card (localSubgroup hA hB) = 1331 := by
  obtain ⟨f, hf, hX, hY, hZ⟩ :=
    coordinate_embedding_of_relations
      (localX (a hA) (b hB)) (localY (a hA) (b hB))
      (localZ (a hA) (b hB)) (matrix_elevenRelations hA hB)
  exact local_card_of_coordinate_embedding hA hB f hf hX hY hZ

/-- Every order-eleven element of the concrete local subgroup is covered by
the central or noncentral representative. -/
theorem local_coverage (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    ∀ w : Model, w ∈ localSubgroup hA hB → orderOf w = 11 →
      ∃ (j : Fin 2) (n : ℕ) (g : Model),
        localRepresentative (a hA) (b hB) j = g * w ^ n * g⁻¹ := by
  obtain ⟨f, _hf, hX, hY, hZ⟩ :=
    coordinate_embedding_of_relations
      (localX (a hA) (b hB)) (localY (a hA) (b hB))
      (localZ (a hA) (b hB)) (matrix_elevenRelations hA hB)
  exact local_coverage_of_coordinate_embedding hA hB f hX hY hZ
    (matrix_elevenNormalizerRelations hA hB)

end Janko4.Simplicity.Elevens

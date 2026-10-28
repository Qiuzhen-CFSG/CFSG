module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.Ambient
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage.Decomposability
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage.DeterminantalLocus
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage.Reconstruction

/-!
# Closedness of the full-flag Plücker image

The simultaneous wedge-annihilator rank conditions characterize the actual
full-flag image. Their diagonal cases force every exterior line to be
decomposable. The mixed cases give inclusion of the recovered subspaces,
which extend to the natural-indexed full flag with its constant top tail.

The determinantal equations already define a closed subset of the scheme
product of projective exterior powers. Combining its rational-point criterion
with this reconstruction proves closedness of the Plücker image for every
choice of coordinate bases, including the empty product in dimension zero.
No decomposability, incidence or geometric closedness premise remains.

Source: the projective flag variety used in Borel, *Linear Algebraic Groups*,
§11.1 (`refs/KGroup/Bor1/Chapter4.tex`).
-/

public section

open scoped ExteriorAlgebra LinearAlgebra.Projectivization

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry

universe u v
variable {k : Type u} [Field k] {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The rank conditions alone characterize full-flag exterior tuples: their
diagonal cases supply all the decomposability needed for reconstruction. -/
theorem mem_range_flagPlucker_iff_rankConditions
    (p : (i : Fin (Module.finrank k V)) → ℙ k (⋀[k]^(i : ℕ) V)) :
    p ∈ Set.range (flagPlucker (k := k) (V := V)) ↔ FlagRankConditions p := by
  rw [mem_range_flagPlucker_iff]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    intro i
    exact (exists_subspacePlucker_iff_le_finrank_pluckerAnnihilator i (p i)).mpr
      (h.le_finrank_annihilator i)

variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [IsAlgClosed k]

/-- Exact image comparison in the ambient scheme, with arbitrary exterior
coordinate bases and no additional realizability hypothesis. -/
theorem mem_range_flagEmbedding_iff_rankConditions
    (b : CoordinateBases (k := k) V) (x : Variety.Geometric.Point (flagAmbient (k := k) V)) :
    x ∈ Set.range (flagEmbedding b) ↔ FlagRankConditions (ambientPointEquiv b x) := by
  rw [mem_range_flagEmbedding_iff, ← mem_range_flagPlucker_iff,
    mem_range_flagPlucker_iff_rankConditions]

/-- The actual full-flag Plücker image is the rational-point locus of a closed
subset of the ambient scheme product of projective exterior powers. -/
theorem exists_flagEmbedding_locus (b : CoordinateBases (k := k) V) :
    ∃ Z : TopologicalSpace.Closeds (flagAmbient (k := k) V).toScheme,
      ∀ x : Variety.Geometric.Point (flagAmbient (k := k) V),
        x.val (IsLocalRing.closedPoint k) ∈ Z ↔ x ∈ Set.range (flagEmbedding b) := by
  obtain ⟨Z, hZ⟩ := exists_flagRankConditions_locus b
  exact ⟨Z, fun x => (hZ x).trans (mem_range_flagEmbedding_iff_rankConditions b x).symm⟩

end Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry

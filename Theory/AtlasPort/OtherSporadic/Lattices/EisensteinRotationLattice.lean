/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/EisensteinRotationLattice.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.EisensteinRational

/-!
# Eisenstein Rotation Lattice

Scalar rotation preserves the rational Eisenstein lattice. Integral omega multiplication supplies preimages under the coordinate embedding.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/EisensteinRotationLattice.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for the source coordinate computations.
-/

@[expose] public section

namespace Atlas.Lattices
open Atlas.Algebra

/-- Integral scalar multiplication agrees with the rational scalar rotation. -/
theorem eisensteinCoordinateEmbedding_omega (z : EisensteinCoordinates) :
    eisensteinCoordinateEmbedding (eisensteinOmega • z) =
      eisensteinRotation (eisensteinCoordinateEmbedding z) := by
  funext i
  change eisensteinToRational (eisensteinOmega * z i) =
    rationalOmega * eisensteinToRational (z i)
  rw [map_mul]
  rfl

/-- The actual integral congruence lattice is invariant under omega. -/
theorem eisensteinRotation_mem_rationalLattice
    {z : EisensteinRationalCoordinates} (hz : z ∈ rationalEisensteinLattice) :
    eisensteinRotation z ∈ rationalEisensteinLattice := by
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨eisensteinOmega • w, eisensteinLeechModule.smul_mem eisensteinOmega hw,
    eisensteinCoordinateEmbedding_omega w⟩

/-- Rotation preserves the rational image of the integral lattice in both directions. -/
theorem eisensteinRotation_lattice_iff (z : EisensteinRationalCoordinates) :
    z ∈ rationalEisensteinLattice ↔ eisensteinRotation z ∈ rationalEisensteinLattice := by
  constructor
  · exact eisensteinRotation_mem_rationalLattice
  · intro hz
    have h := eisensteinRotation_mem_rationalLattice
      (eisensteinRotation_mem_rationalLattice hz)
    rwa [eisensteinRotation_cube] at h

end Atlas.Lattices

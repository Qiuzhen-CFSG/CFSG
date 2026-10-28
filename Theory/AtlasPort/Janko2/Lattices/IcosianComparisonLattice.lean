/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianComparisonLattice.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianComparisonReverse
public import Theory.AtlasPort.Janko2.Lattices.IcosianComparisonForwardChecks
public import Theory.AtlasPort.Janko2.Lattices.IcosianGenerators

/-!
# Icosian Comparison Lattice

The rational comparison maps the actual icosian congruence lattice onto
the Golay Leech lattice. Forward generator checks and the independently
proved reverse containment establish both membership directions.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianComparisonLattice.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

/-- Every vector of the specified right-icosian module maps into the retained Golay Leech lattice. -/
theorem icosianComparison_forward (z : IcosianRationalCoordinates)
    (hz : z ∈ rationalIcosianLattice) : icosianComparison z ∈ rationalLeech := by
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hz
  let S : Submodule ℤ IcosianCoordinates := rationalLeech.comap
    ((icosianComparison.toLinearMap.restrictScalars ℤ).comp icosianCoordinateEmbedding)
  have h (j : Fin 36) : icosianComparisonSourceGenerator j ∈ S := by
    obtain ⟨x,hx,he⟩ := icosianComparison_generator_check j
    change icosianComparison (icosianCoordinateEmbedding _) ∈ rationalLeech
    rw [he]
    exact Submodule.mem_map.mpr ⟨x,hx,rfl⟩
  exact (icosianLeechModule_le_of_generators S h) hv

/-- Both actual containments, with the specified integral module and retained Golay construction. -/
theorem icosianComparison_lattice_iff (z : IcosianRationalCoordinates) :
    z ∈ rationalIcosianLattice ↔ icosianComparison z ∈ rationalLeech := by
  constructor
  · exact icosianComparison_forward z
  · intro h
    simpa only [LinearEquiv.symm_apply_apply] using
      icosianComparison_reverse (icosianComparison z) h

/-- The specified module maps onto every retained Leech vector. -/
theorem icosianComparison_lattice_surjective (x : RationalCoordinates)
    (hx : x ∈ rationalLeech) :
    ∃ z ∈ rationalIcosianLattice, icosianComparison z=x :=
  ⟨icosianComparison.symm x,icosianComparison_reverse x hx,icosianComparison.apply_symm_apply x⟩

end Atlas.Lattices

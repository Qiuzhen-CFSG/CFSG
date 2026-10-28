/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianComparisonReverse.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianComparisonReverseChecks

/-!
# Icosian Comparison Reverse

Every Golay Leech vector has its inverse image in the actual icosian
congruence lattice. The proof applies the Leech generator criterion to
the submodule defined by inverse-image membership.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianComparisonReverse.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

private theorem oldPoint_coordinateIndex (i : Omega) :
    icosianOldPoint (icosianLeechCoordinateIndex i) = i := by
  revert i; decide +kernel

/-- The inverse rational isometry maps every retained Golay Leech vector into the
actual right-icosian congruence module, using all retained integral generators. -/
theorem icosianComparison_reverse (x : RationalCoordinates)
    (hx : x ∈ rationalLeech) : icosianComparison.symm x ∈ rationalIcosianLattice := by
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
  let P : Submodule ℤ IntegerCoordinates := rationalIcosianLattice.comap
    ((icosianComparison.symm.toLinearMap.restrictScalars ℤ).comp rationalEmbedding)
  have h (j : Fin 38) : icosianComparisonTargetGenerator j ∈ P := by
    change icosianComparison.symm (rationalEmbedding _) ∈ rationalIcosianLattice
    rw [← icosianComparison_preimage_check, icosianComparison.symm_apply_apply]
    exact Submodule.mem_map.mpr ⟨_, icosianComparisonPreimage_mem j, rfl⟩
  have hp : leech ≤ P := leech_le_of_generators P ((0,0),0)
    (fun i => by
      have hi := h ⟨(icosianLeechCoordinateIndex i).val, by omega⟩
      simpa [icosianComparisonTargetGenerator, (icosianLeechCoordinateIndex i).isLt,
        oldPoint_coordinateIndex] using hi)
    (by simpa [icosianComparisonTargetGenerator] using h 24)
    (fun j => by
      have hj := h ⟨j.val+25, by omega⟩
      simpa [icosianComparisonTargetGenerator, show ¬j.val+25<24 by omega,
        show j.val+25≠24 by omega, show j.val+25<37 by omega] using hj)
    (by simpa [icosianComparisonTargetGenerator] using h 37)
  exact hp hv

end Atlas.Lattices

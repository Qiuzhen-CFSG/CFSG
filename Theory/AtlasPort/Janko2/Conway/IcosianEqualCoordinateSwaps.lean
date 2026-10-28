/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianEqualCoordinateSwaps.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianLocalAOrbit

/-!
# IcosianEqualCoordinateSwaps

Equal coordinates of a root admit a fixing monomial swap. This symmetry supplies the
coordinate permutations needed for local orbit transport.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianEqualCoordinateSwaps.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- Equal coordinates give an actual monomial line stabilizer element. -/
theorem icosianEqualCoordinate_swap_fixes (r : IcosianRoot) (i j : Fin 3)
    (h : r.val i=r.val j) :
    icosianMonomialToHermitian (icosianPureBlockPermutation (Equiv.swap i j)) •
      icosianRootPoint r=icosianRootPoint r := by
  apply (icosianMonomial_line_iff _ _).mpr
  refine ⟨1,?_⟩
  intro k
  change (1 : IcosianQuaternion)*(r.val ((Equiv.swap i j).symm k)).val=
    (r.val k).val*1
  simp only [one_mul,mul_one,Equiv.symm_swap]
  by_cases hki : k=i
  · subst k; simp [h]
  by_cases hkj : k=j
  · subst k; simp [h]
  rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

end Atlas.Conway

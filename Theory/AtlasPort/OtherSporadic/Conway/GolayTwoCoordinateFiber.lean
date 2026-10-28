/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/GolayTwoCoordinateFiber.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.GolayCoordinateSeparation
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechVisibleSymmetries
public import Mathlib.LinearAlgebra.Dimension.Finite
/-!
Golay coordinate restrictions and signed-support transport in the Leech lattice.
The proofs retain the explicit code maps and coordinate identities used by the stabilizer geometry.

Source: Gerald Höhn, `Atlas/Conway/GolayTwoCoordinateFiber.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

def golayTwoCoordinateProjection (i j : Omega) : golay →ₗ[Bit] Bit × Bit where
  toFun c := (c.val i,c.val j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem golay_two_coordinates_surjective (i j : Omega) (hij : i ≠ j) :
    Function.Surjective (golayTwoCoordinateProjection i j) := by
  obtain ⟨c,hc⟩ := golay_coordinate_separates i j hij
  let w : golay := ⟨allOnes,C0_le_golay allOnes_mem_C0⟩
  have hw (k : Omega) : w.val k = 1 := rfl
  have h01 : ∃ c : golay, c.val i = 0 ∧ c.val j = 1 := by
    rcases bit_cases (c.val i) with hi | hi <;> rcases bit_cases (c.val j) with hj | hj
    · exact False.elim (hc (hi.trans hj.symm))
    · exact ⟨c,hi,hj⟩
    · refine ⟨c+w,?_,?_⟩ <;> change c.val _ + w.val _ = _ <;> simp [hi,hj,hw]
    · exact False.elim (hc (hi.trans hj.symm))
  obtain ⟨d,hi,hj⟩ := h01
  rintro ⟨a,b⟩
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨d,Prod.ext hi hj⟩
  · refine ⟨d+w,?_⟩
    apply Prod.ext <;> change d.val _ + w.val _ = _ <;> simp [hi,hj,hw]
  · exact ⟨w,rfl⟩

theorem golay_two_coordinate_kernel_finrank (i j : Omega) (hij : i ≠ j) :
    Module.finrank Bit (golayTwoCoordinateProjection i j).ker = 10 := by
  have he := (golayTwoCoordinateProjection i j).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (golay_two_coordinates_surjective i j hij),
    finrank_top,golay_finrank,Module.finrank_prod,Module.finrank_self] at he
  omega

theorem golay_two_coordinate_kernel_card (i j : Omega) (hij : i ≠ j) :
    Nat.card (golayTwoCoordinateProjection i j).ker = 1024 := by
  rw [Module.natCard_eq_pow_finrank (K := Bit),golay_two_coordinate_kernel_finrank i j hij]
  simp [Bit]

end Atlas.Conway


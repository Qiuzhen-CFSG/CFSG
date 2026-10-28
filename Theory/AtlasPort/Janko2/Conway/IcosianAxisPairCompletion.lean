/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianAxisPairCompletion.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianAxisOrthogonalCompletion

/-!
# IcosianAxisPairCompletion

The coordinate axes form an orthogonal frame. Single-support root lines and
coordinate orthogonality prove the third axis is its unique completion.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianAxisPairCompletion.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- A root supported on one coordinate gives exactly the corresponding actual axis line. -/
theorem icosianRootPoint_of_single_support (r : IcosianRoot) (i : Fin 3)
    (hz : ∀ j,j≠i → r.val j=0) : icosianRootToPoint r=icosianRootAxisPoint i := by
  apply Subtype.ext
  rw [icosianRootAxisPoint_val]
  apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
  refine ⟨MulOpposite.op (r.val i).val,?_⟩
  funext j
  by_cases hj : j=i
  · subst j
    simp [icosianCoordinateEmbedding]
  · change (Pi.single i (1 : IcosianQuaternion) : IcosianRationalCoordinates) j*(r.val i).val=(r.val j).val
    rw [hz j hj]
    simp [hj]

theorem icosianRootAxisPoints_orthogonal (i j : Fin 3) (hij : i≠j) :
    IcosianRootPointOrthogonal (icosianRootAxisPoint i) (icosianRootAxisPoint j) := by
  apply (icosianRootAxisPoint_orthogonal_iff i (icosianAxisRoot (j,1))).mpr
  simp [icosianAxisRoot,icosianSingle,hij]

/-- Two distinct coordinate axes have the remaining coordinate axis as their unique root-line complement. -/
theorem icosianRootAxisPair_complement_unique (i j k : Fin 3)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) (p : IcosianRootPoint)
    (hi : IcosianRootPointOrthogonal (icosianRootAxisPoint i) p)
    (hj : IcosianRootPointOrthogonal (icosianRootAxisPoint j) p) : p=icosianRootAxisPoint k := by
  obtain ⟨r,rfl⟩ := icosianRootToPoint_surjective p
  have hri := (icosianRootAxisPoint_orthogonal_iff i r).mp hi
  have hrj := (icosianRootAxisPoint_orthogonal_iff j r).mp hj
  apply icosianRootPoint_of_single_support r k
  intro l hl
  have hc : l=i ∨ l=j := by omega
  rcases hc with rfl | rfl
  · exact hri
  · exact hrj

end Atlas.Conway

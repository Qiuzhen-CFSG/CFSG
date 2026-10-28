/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLTrianglePrimitivity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLTriangleOrbits
public import Theory.AtlasPort.OtherSporadic.Combinatorics.FiniteFiberPartition
public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
Primitivity of the 2025-triangle action.
A block through the base triangle is a union of stabilizer orbits; the four
subdegrees and divisibility of its size force a singleton or the whole set.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLTrianglePrimitivity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices Atlas.Combinatorics MulAction
open scoped Pointwise BigOperators
attribute [local instance] Classical.propDecidable

set_option maxRecDepth 10000 in
theorem mcl_triangle_block_divisibility (T : Finset (Fin 4)) (h0 : 0 ∈ T)
    (hd : (∑ t ∈ T,mclTriangleSize t) ∣ 2025) : T = {0} ∨ T = Finset.univ := by
  revert hd h0 T
  decide +kernel

theorem mcl_triangle_block_saturated (B : Set McLTriangles)
    (ha : mclBaseTriangle ∈ B) (hB : IsBlock McLModel B)
    (x : McLTriangles) (hx : x ∈ B) (y : McLTriangles)
    (ht : mclTriangleType x = mclTriangleType y) : y ∈ B := by
  obtain ⟨g,hg⟩ := (mcl_triangle_mathieu_orbit_iff x y).mpr ht
  have hfix : (mclMathieu22Embedding g) • B = B :=
    hB.stabilizer_le ha (mclMathieuTriangleEmbedding g).prop
  rw [← hg,← hfix,Set.smul_mem_smul_set_iff]
  exact hx

theorem mcl_triangles_primitive : IsPreprimitive McLModel McLTriangles := by
  let := mcl_triangles_transitive
  apply IsPreprimitive.of_isTrivialBlock_base mclBaseTriangle
  intro B ha hB
  let T := fiberLabels mclTriangleType B
  have hs := mcl_triangle_block_saturated B ha hB
  have hmem (y : McLTriangles) : mclTriangleType y ∈ T ↔ y ∈ B :=
    mem_fiberLabels _ _ hs y
  have h0 : (0 : Fin 4) ∈ T := by
    rw [← mcl_base_triangle_type]
    exact (hmem _).mpr ha
  have hc : Nat.card B = ∑ t ∈ T,mclTriangleSize t :=
    saturated_set_card _ _ mcl_triangle_type_card B hs
  have hd : (∑ t ∈ T,mclTriangleSize t) ∣ 2025 := by
    rw [← hc,← mcl_triangles_card]
    exact hB.ncard_dvd_card ⟨_,ha⟩
  rcases mcl_triangle_block_divisibility T h0 hd with ht | ht
  · left
    apply B.ncard_le_one_iff_subsingleton.mp
    change Nat.card B ≤ 1
    rw [hc,ht]
    simp [mclTriangleSize]
  · right
    apply Set.eq_univ_of_forall
    intro y
    apply (hmem y).mp
    rw [ht]; exact Finset.mem_univ _

end Atlas.Conway

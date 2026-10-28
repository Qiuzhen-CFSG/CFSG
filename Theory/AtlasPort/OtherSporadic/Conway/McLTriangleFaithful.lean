/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLTriangleFaithful.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLTrianglePrimitivity
public import Theory.AtlasPort.OtherSporadic.Conway.McLStronglyRegular
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SimpleStabilizerFaithful

/-!
Faithfulness of the primitive triangle action.
The 22-point orbit in the transitive 275-vertex action rules out normality of
the simple Mathieu22 stabilizer, forcing the triangle-action kernel to be trivial.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLTriangleFaithful.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction
attribute [local instance] Classical.propDecidable

theorem mcl_triangle_stabilizer_graph_orbit (c : McLPointLabels) :
    orbit McLTriangleStabilizer (mclWittVector (Sum.inl c)) =
      Set.range (fun d : McLPointLabels => mclWittVector (Sum.inl d)) := by
  rw [← mcl_point_family_orbit c]
  ext y
  constructor
  · rintro ⟨g,rfl⟩
    obtain ⟨h,rfl⟩ := mclMathieuTriangleEquiv.surjective g
    exact mem_orbit_iff.mpr ⟨h,rfl⟩
  · rintro ⟨g,rfl⟩
    exact mem_orbit_iff.mpr ⟨mclMathieuTriangleEquiv g,rfl⟩

theorem mcl_triangle_stabilizer_not_normal : ¬ McLTriangleStabilizer.Normal := by
  intro hn
  let := hn
  let := mcl_graph_transitive
  let c := mclBaseGraphLabel
  have hB : IsBlock McLModel (orbit McLTriangleStabilizer (mclWittVector (Sum.inl c))) :=
    IsBlock.orbit_of_normal _
  have hd := hB.ncard_dvd_card ⟨_,mem_orbit_self _⟩
  rw [mcl_triangle_stabilizer_graph_orbit] at hd
  change Nat.card (Set.range (fun d : McLPointLabels => mclWittVector (Sum.inl d))) ∣
    Nat.card McLGraphPoints at hd
  rw [mcl_point_family_card,mcl_graph_card] at hd
  exact (by decide : ¬22 ∣ 275) hd

theorem mcl_triangles_faithful : FaithfulSMul McLModel McLTriangles := by
  let := mcl_triangle_stabilizer_simple
  exact Atlas.GroupTheory.faithful_of_simple_stabilizer_not_normal mclBaseTriangle
    mcl_triangle_stabilizer_not_normal

end Atlas.Conway

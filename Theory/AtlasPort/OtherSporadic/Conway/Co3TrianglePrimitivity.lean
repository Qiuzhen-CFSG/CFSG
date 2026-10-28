/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TrianglePrimitivity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleTransitivity
public import Mathlib.GroupTheory.GroupAction.Primitive
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TrianglePrimitivity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices Atlas.Combinatorics MulAction
open scoped Pointwise BigOperators
attribute [local instance] Classical.propDecidable

def co3TriangleBlockCandidate : Set (Co3Triangles co3MarkedCoordinate) :=
  {y | co3TriangleType co3MarkedCoordinate y ∈ ({0,1,3} : Finset (Fin 8))}

theorem co3_triangle_candidate_not_block : ¬ IsBlock Co3MarkedModel co3TriangleBlockCandidate := by
  intro hB
  obtain ⟨g,hbase,hpair⟩ := co3_triangle_two_fusions
  have h0 : co3BaseTriangle co3MarkedCoordinate ∈ co3TriangleBlockCandidate := by
    change co3TriangleType co3MarkedCoordinate _ ∈ ({0,1,3} : Finset (Fin 8))
    rw [co3_base_triangle_type]; simp
  have h1 : co3TrianglePair ∈ co3TriangleBlockCandidate := by
    change co3TriangleType co3MarkedCoordinate _ ∈ ({0,1,3} : Finset (Fin 8))
    rw [co3TrianglePair_type]; simp
  have h3 : g • co3BaseTriangle co3MarkedCoordinate ∈ co3TriangleBlockCandidate := by
    change co3TriangleType co3MarkedCoordinate _ ∈ ({0,1,3} : Finset (Fin 8))
    rw [hbase]; simp
  have hfix : g • co3TriangleBlockCandidate = co3TriangleBlockCandidate := by
    have he := hB.smul_eq_smul_of_nonempty (g₁ := g) (g₂ := 1)
      ⟨g • co3BaseTriangle co3MarkedCoordinate,
        (Set.smul_mem_smul_set_iff).mpr h0,by simpa using h3⟩
    simpa using he
  have h5 : g • co3TrianglePair ∈ co3TriangleBlockCandidate := by
    rw [← hfix]
    exact (Set.smul_mem_smul_set_iff).mpr h1
  change co3TriangleType _ _ ∈ ({0,1,3} : Finset (Fin 8)) at h5
  rw [hpair] at h5
  exact (by decide : (5 : Fin 8) ∉ ({0,1,3} : Finset (Fin 8))) h5

theorem co3_triangle_block_saturated (B : Set (Co3Triangles co3MarkedCoordinate))
    (ha : co3BaseTriangle co3MarkedCoordinate ∈ B) (hB : IsBlock Co3MarkedModel B)
    (x : Co3Triangles co3MarkedCoordinate) (hx : x ∈ B) (y : Co3Triangles co3MarkedCoordinate)
    (ht : co3TriangleType co3MarkedCoordinate x = co3TriangleType co3MarkedCoordinate y) : y ∈ B := by
  obtain ⟨g,hg⟩ := (co3_triangle_mathieu_orbit_iff co3MarkedCoordinate x y).mpr ht
  have hfix : (mathieu23ToNormSixStabilizer co3MarkedCoordinate g) • B = B :=
    hB.stabilizer_le ha (Subtype.ext (mathieu23_fixes_triangle co3MarkedCoordinate g))
  rw [← hg,← hfix,Set.smul_mem_smul_set_iff]
  exact hx

theorem co3_triangles_primitive : IsPreprimitive Co3MarkedModel (Co3Triangles co3MarkedCoordinate) := by
  let := co3_triangles_transitive
  apply IsPreprimitive.of_isTrivialBlock_base (co3BaseTriangle co3MarkedCoordinate)
  intro B ha hB
  let T := fiberLabels (co3TriangleType co3MarkedCoordinate) B
  have hs := co3_triangle_block_saturated B ha hB
  have hmem (y : Co3Triangles co3MarkedCoordinate) : co3TriangleType co3MarkedCoordinate y ∈ T ↔ y ∈ B :=
    mem_fiberLabels _ _ hs y
  have h0 : (0 : Fin 8) ∈ T := by
    rw [← co3_base_triangle_type]
    exact (hmem _).mpr ha
  have hc : Nat.card B = ∑ t ∈ T,co3TriangleSize t :=
    saturated_set_card _ _ (co3_triangle_type_card co3MarkedCoordinate) B hs
  have hd : (∑ t ∈ T,co3TriangleSize t) ∣ 48600 := by
    rw [← hc,← co3_triangles_card co3MarkedCoordinate]
    exact hB.ncard_dvd_card ⟨_,ha⟩
  rcases co3_triangle_block_divisibility T h0 hd with ht | ht | ht
  · left
    apply B.ncard_le_one_iff_subsingleton.mp
    change Nat.card B ≤ 1
    rw [hc,ht]
    simp [co3TriangleSize]
  · have he : B = co3TriangleBlockCandidate := by
      ext y
      rw [← hmem y,ht]
      rfl
    exact False.elim (co3_triangle_candidate_not_block (he ▸ hB))
  · right
    apply Set.eq_univ_of_forall
    intro y
    apply (hmem y).mp
    rw [ht]; exact Finset.mem_univ _

end Atlas.Conway

/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/Conway3Geometry.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway3
public import Theory.AtlasPort.OtherSporadic.Conway.Co3DecompositionFaithful
public import Theory.AtlasPort.OtherSporadic.Conway.Co3MathieuOrbits
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Sporadic/Conway3Geometry.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.Conway3
open Atlas.Codes Atlas.Lattices Atlas.Conway

abbrev Points := MinimumDecompositions vector.val
abbrev PointHeptad := Co3PointHeptad ((0,0),0)

def pointHeptadEquiv : PointHeptad ≃ Points := co3PointHeptadDecompositionEquiv _

theorem degree : Nat.card Points = 276 := co3_decompositions_card _

theorem faithful : FaithfulSMul Model Points := co3_decompositions_faithful

theorem pointHeptad_equivariant (g : Mathieu23PointModel ((0,0),0)) (p : PointHeptad) :
    pointHeptadEquiv (co3PointHeptadMap _ g p) = mathieu23Embedding g • pointHeptadEquiv p :=
  co3PointHeptadDecomposition_equivariant _ g p

def triangleVector : leech := oddMinimumVector ((0,0),0) 0

abbrev TriangleStabilizer := MulAction.stabilizer Model triangleVector

def triangleMathieuEquiv : Mathieu23PointModel ((0,0),0) ≃* TriangleStabilizer :=
  mathieu23TriangleEquiv _

theorem triangle_stabilizer_card : Nat.card TriangleStabilizer = 10200960 := by
  rw [← Nat.card_congr triangleMathieuEquiv.toEquiv,mathieu23_order]

theorem triangle_norms : integerDot triangleVector.val triangleVector.val = 32 ∧
    integerDot (vector.val-triangleVector).val (vector.val-triangleVector).val = 64 :=
  co3_base_triangle_norms _

theorem exists_mul_ne_mul : ∃ g h : Model, g*h ≠ h*g := by
  obtain ⟨g,h,hne⟩ := mathieu23_noncommuting_pair ((0,0),0)
  refine ⟨mathieu23Embedding g,mathieu23Embedding h,?_⟩
  intro he
  apply hne
  apply mathieu23Embedding_injective
  simpa only [map_mul] using he

end Atlas.Sporadic.Conway3

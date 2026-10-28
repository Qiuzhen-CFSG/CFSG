/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/HigmanSimsLocal.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.HigmanSimsConfiguration
public import Theory.AtlasPort.OtherSporadic.Conway.HSLocalOrbits

/-!
The Mathieu22 local subgroup of the Higman–Sims construction.
The concrete point-stabilizer isomorphism exports order, simplicity, faithfulness, and local orbit counts.

Source: Gerald Höhn, `Atlas/Sporadic/HigmanSimsLocal.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.HigmanSims
open Atlas.Codes Atlas.Lattices Atlas.Conway

abbrev MathieuModel := HSMathieuModel
abbrev PointStabilizer := HSGraphStabilizer

def mathieu22Embedding : MathieuModel →* Model := hsMathieu22Embedding

def pointStabilizerEquiv : MathieuModel ≃* PointStabilizer := hsMathieuGraphEquiv

theorem mathieu22Embedding_injective : Function.Injective mathieu22Embedding := hsMathieu22Embedding_injective

theorem point_stabilizer_card : Nat.card PointStabilizer = 443520 := hs_graph_stabilizer_card

theorem point_stabilizer_simple : IsSimpleGroup PointStabilizer := hs_graph_stabilizer_simple

theorem faithful : FaithfulSMul Model Points := hs_graph_faithful

theorem exists_mul_ne_mul : ∃ g h : Model, g*h ≠ h*g := hs_noncommuting_pair

def localFamily : Points → Fin 3 := hsLocalFamily

def subdegree : Fin 3 → ℕ := hsSubdegree

theorem local_fiber_card (i : Fin 3) : Nat.card {y : Points // localFamily y = i} = subdegree i :=
  hs_local_fiber_card i

theorem local_family_transitive (y z : Points) (h : localFamily y = localFamily z) :
    ∃ g : PointStabilizer, g • y = z := hs_local_family_transitive y z h

theorem point_family_orbit (c : HSPointLabels) :
    MulAction.orbit PointStabilizer (hsPointVector c) = Set.range hsPointVector := hs_stabilizer_point_orbit c

theorem hexad_family_orbit (B : HSHexadLabels) :
    MulAction.orbit PointStabilizer (hsHexadVector B) = Set.range hsHexadVector := hs_stabilizer_hexad_orbit B

end Atlas.Sporadic.HigmanSims

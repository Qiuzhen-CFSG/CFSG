/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalLineLocalOrder.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalLineStabilizer

/-!
The order of the local stabilizer of the distinguished orthogonal minimum line.
Orbit-stabilizer divides the vector-stabilizer order by the orthogonal-line degree.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalLineLocalOrder.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
set_option maxRecDepth 10000

def distinguishedOrthogonalLine (i j : Omega) (hij : i ≠ j) :
    OrthogonalMinimumLines (minimumPairPlus i j) :=
  ⟨antipodalLine (minimumPairMinus i j),minimumPairMinus i j,
    ⟨minimumPairMinus_norm i j hij,minimumPair_orthogonal i j hij⟩,rfl⟩

theorem distinguishedOrthogonalLine_stabilizer (i j : Omega) (hij : i ≠ j) :
    MulAction.stabilizer (fullVectorStabilizer (minimumPairPlus i j))
      (distinguishedOrthogonalLine i j hij) = orthogonalLineStabilizer i j := by
  ext g
  exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩

theorem orthogonalLineStabilizer_order (i j : Omega) (hij : i ≠ j) :
    Nat.card (orthogonalLineStabilizer i j) = 908328960 := by
  let := orthogonalMinimumLines_pretransitive i j hij
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    (fullVectorStabilizer (minimumPairPlus i j)) (distinguishedOrthogonalLine i j hij))
  rw [Nat.card_prod,MulAction.orbit_eq_univ,Nat.card_congr (Equiv.Set.univ _),
    orthogonalMinimumLines_card i j hij,distinguishedOrthogonalLine_stabilizer] at h
  have ho := minimum_vector_stabilizer_order
    (⟨minimumPairPlus i j,minimumPairPlus_norm i j hij⟩ : LeechShell 4)
  change Nat.card (fullVectorStabilizer (minimumPairPlus i j)) = 42305421312000 at ho
  rw [ho] at h
  omega

end Atlas.Conway

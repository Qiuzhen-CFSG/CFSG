/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/Conway2Generation.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway2Commutators
public import Theory.AtlasPort.OtherSporadic.Conway.Co2NormalGeneration
public import Mathlib.GroupTheory.IsPerfect

/-!
Normal generation and perfectness of the actual Conway Co2 model.
The proof specializes the shortened-sign normal closure and commutator calculations.

Source: Gerald Höhn, `Atlas/Sporadic/Conway2Generation.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.Conway2
open Atlas.Conway

def outerPairRestriction := co2PairRestriction
def outerPairSection := co2PairSection

theorem outerPairSection_rightInverse (p : Equiv.Perm Co2MarkedPair) :
    outerPairRestriction (outerPairSection p) = p := co2PairSection_rightInverse p

def embeddedSigns : Subgroup Model := co2Signs

theorem signs_normalClosure : Subgroup.normalClosure (embeddedSigns : Set Model) = ⊤ :=
  co2Signs_normalClosure

theorem commutator_eq_top : commutator Model = ⊤ := co2_commutator_eq_top

theorem perfect : Group.IsPerfect Model := ⟨commutator_eq_top⟩

end Atlas.Sporadic.Conway2

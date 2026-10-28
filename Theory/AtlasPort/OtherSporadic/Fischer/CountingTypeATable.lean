/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Fischer/CountingTypeATable.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Fischer.CountingColumnArithmetic

/-!
# CountingTypeATable

The fourteen Type A histogram rows, calculated over the fifteen pairs of
columns. Kernel reduction verifies the explicit finite sums; identification
with actual source octads is supplied by the later interpretation modules.

Source: Gerald Höhn, ATLAS, `Atlas/Fischer/CountingTypeATable.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and narrow arithmetic imports.
Definitions remain exposed for the downstream finite calculations.
-/

@[expose] public section

namespace Atlas.Fischer

/-- The fourteen normalized source profiles in the complete three-type subtotal table. -/
def countingTableProfile (r : Fin 14) : CountingColumnVector :=
  ![![4,0,4,0,0,0],![4,0,0,4,0,0],![0,0,4,4,0,0],
    ![0,0,2,2,2,2],![2,2,2,2,0,0],![2,2,0,2,2,0],![3,1,1,1,1,1],
    ![0,0,4,4,0,0],![0,0,4,0,4,0],![0,0,2,2,2,2],
    ![4,0,4,0,0,0],![2,2,2,2,0,0],![2,2,2,0,2,0],![3,1,1,1,1,1]] r

def countingTableEpsilon (r : Fin 14) : ℕ := if r.val<7 then 0 else 1

def countingTableD : Finset (Fin 6) := {0,1}
def countingTableE (r : Fin 14) : Finset (Fin 6) := if r.val<7 then {0,2} else {2,3}
def countingTableF (r : Fin 14) : Finset (Fin 6) := if r.val<7 then {1,2} else {4,5}

def countingTypeAColumnProfile (T : Finset (Fin 6)) : CountingColumnVector :=
  fun i => if i ∈ T then 4 else 0

def countingTypeATargetWeight (r : Fin 14) (T : Finset (Fin 6)) : Option ℤ :=
  countingColumnWeight (countingTableEpsilon r) countingTableD (countingTableE r) (countingTableF r)
    (countingTableProfile r) (countingTypeAColumnProfile T)
    (fun i => if i ∈ T then countingTableProfile r i else 0)

def countingTypeATargetHistogram (r : Fin 14) : CountingSignedHistogram :=
  fun j => ∑ T ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2,
    countingWeightHistogram (countingTypeATargetWeight r T) j

/-- Exact source Type A subtotals, with columns -9,-3,-1,1,3,9. -/
def countingTypeAExpectedHistogram (r : Fin 14) : CountingSignedHistogram :=
  ![![0,0,0,4,6,3],![0,4,0,2,6,0],![2,4,0,0,4,2],
    ![0,0,0,0,0,0],![0,0,0,4,2,0],![0,0,0,0,0,0],![0,0,0,1,0,0],
    ![0,0,0,4,8,1],![0,4,0,2,4,2],![0,0,0,4,2,0],
    ![0,2,4,4,2,0],![0,0,0,4,2,0],![0,0,0,0,0,0],![0,0,0,2,0,0]] r

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- The finite check evaluates fourteen profiles against fifteen column pairs.
/-- All fourteen Type A target rows, over the fifteen actual two-column choices.
This arithmetic lemma is separate from interpretation by the actual octad column bridge. -/
theorem countingTypeATargetHistogram_all :
    ∀ r : Fin 14, countingTypeATargetHistogram r=countingTypeAExpectedHistogram r := by
  decide

end Atlas.Fischer

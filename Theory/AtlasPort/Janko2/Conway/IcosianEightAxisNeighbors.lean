/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianEightAxisNeighbors.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianAxisCompletion
public import Theory.AtlasPort.Janko2.Algebra.IcosianParityIntegral

/-!
# IcosianEightAxisNeighbors

Eight explicit edge-root lines are orthogonal neighbors of the first axis. Norm,
reduction, and injectivity calculations distinguish these points.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianEightAxisNeighbors.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped Matrix Quaternion

/-- Doubled quaternion coordinates of the eight local norm-two scalars.
The local catalogue is proved exhaustive using the independent ten-neighbor count. -/
def icosianEightNeighborData : Fin 8 → IcosianIntegerCoordinates := ![
  ![-2,0,-2,0,0,0,0,0], ![-2,0,2,0,0,0,0,0],
  ![0,0,0,0,-2,0,-2,0], ![0,0,0,0,-2,0,2,0],
  ![0,0,0,0,2,0,-2,0], ![0,0,0,0,2,0,2,0],
  ![2,0,-2,0,0,0,0,0], ![2,0,2,0,0,0,0,0]]

def icosianEightNeighborScalar (i : Fin 8) : icosianOrder :=
  icosianIntegralSynthesis (icosianParityIntegralCoefficients (icosianEightNeighborData i))

theorem icosianEightNeighborScalar_norm (i : Fin 8) :
    icosianNorm (icosianEightNeighborScalar i).val=2 := by
  fin_cases i <;> decide +kernel

theorem icosianEightNeighborScalar_reduction (i : Fin 8) :
    icosianModuloTwo (icosianEightNeighborScalar i)=!![0,1;0,0] := by
  rw [icosianEightNeighborScalar,icosianModuloTwo_synthesis]
  fin_cases i <;> decide +kernel

theorem icosianEightNeighborScalar_injective : Function.Injective
    (fun i => (icosianEightNeighborScalar i).val) := by
  have hc : ∀ i j : Fin 8,
      ((icosianEightNeighborScalar i).val.re=(icosianEightNeighborScalar j).val.re ∧
       (icosianEightNeighborScalar i).val.imI=(icosianEightNeighborScalar j).val.imI ∧
       (icosianEightNeighborScalar i).val.imJ=(icosianEightNeighborScalar j).val.imJ ∧
       (icosianEightNeighborScalar i).val.imK=(icosianEightNeighborScalar j).val.imK) → i=j := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  intro i j h
  exact hc i j ⟨congrArg QuaternionAlgebra.re h,congrArg QuaternionAlgebra.imI h,
    congrArg QuaternionAlgebra.imJ h,congrArg QuaternionAlgebra.imK h⟩

def icosianEightNeighborPair (i : Fin 8) : IcosianEdgePair :=
  ⟨(⟨icosianEightNeighborScalar 0,icosianEightNeighborScalar_norm 0⟩,
    ⟨icosianEightNeighborScalar i,icosianEightNeighborScalar_norm i⟩),
    by rw [icosianEightNeighborScalar_reduction,icosianEightNeighborScalar_reduction],
    by intro j; rw [icosianEightNeighborScalar_reduction]; fin_cases j <;> rfl⟩

def icosianEightNeighborRoot (i : Fin 8) : IcosianRoot := icosianEdgeRootBase (icosianEightNeighborPair i)
def icosianEightNeighborPoint (i : Fin 8) : IcosianAxisNeighbor :=
  icosianZeroRootToNeighbor ⟨icosianEightNeighborRoot i,icosianEdgeRootBase_zero _⟩

theorem icosianEightNeighborPoint_injective : Function.Injective icosianEightNeighborPoint := by
  intro i j h
  have hp : icosianRootPoint (icosianEightNeighborRoot i)=icosianRootPoint (icosianEightNeighborRoot j) :=
    congrArg (fun p : IcosianAxisNeighbor => p.val.val) h
  obtain ⟨u,hu⟩ := (icosianRootPoint_eq_iff (icosianEightNeighborRoot j) (icosianEightNeighborRoot i)).mp hp
  have h1 := congrArg (fun r : IcosianRoot => (r.val 1).val) hu
  have hn : (icosianEightNeighborScalar 0).val≠0 := by
    intro hz
    have ht := icosianEightNeighborScalar_norm 0
    rw [hz] at ht
    norm_num [icosianNorm] at ht
  change (icosianEightNeighborScalar 0).val=(icosianEightNeighborScalar 0).val*u.val.val at h1
  have hu1 : u.val.val=1 := mul_left_cancel₀ hn (h1.symm.trans (mul_one _).symm)
  have h2 := congrArg (fun r : IcosianRoot => (r.val 2).val) hu
  change (icosianEightNeighborScalar i).val=(icosianEightNeighborScalar j).val*u.val.val at h2
  rw [hu1,mul_one] at h2
  exact icosianEightNeighborScalar_injective h2

end Atlas.Conway

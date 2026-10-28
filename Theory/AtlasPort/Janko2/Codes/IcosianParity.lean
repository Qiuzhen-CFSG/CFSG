/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/IcosianParity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.Alphabets

/-!
# IcosianParity

The binary parity code of the four icosian basis coordinates has
sixteen words. Kernel-checked finite calculations identify zero, the
all-ones word, and fourteen tetrad supports.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/IcosianParity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators

/-- Parities of twice the four half-integral golden-order basis vectors. -/
def icosianParityRows : Fin 4 → Fin 8 → Bit :=
  ![![1,0,1,1,0,0,0,1], ![0,1,1,0,0,0,1,1],
    ![1,1,1,0,0,1,0,0], ![1,0,0,1,1,1,0,0]]

def icosianParityEncoder : (Fin 4 → Bit) →ₗ[Bit] (Fin 8 → Bit) where
  toFun a j := ∑ i, a i * icosianParityRows i j
  map_add' a b := by ext j; simp [add_mul,Finset.sum_add_distrib]
  map_smul' r a := by ext j; simp [Finset.mul_sum,mul_assoc]

def icosianParity : Submodule Bit (Fin 8 → Bit) := icosianParityEncoder.range

theorem icosianParityEncoder_injective : Function.Injective icosianParityEncoder := by
  decide +kernel

def icosianTetradPositions : Fin 14 → Fin 4 → Fin 8 :=
  ![![0,2,3,7], ![1,2,6,7], ![0,1,3,6], ![0,1,2,5],
    ![1,3,5,7], ![0,5,6,7], ![2,3,5,6], ![0,3,4,5],
    ![2,4,5,7], ![1,4,5,6], ![1,2,3,4], ![0,1,4,7],
    ![3,4,6,7], ![0,2,4,6]]

def icosianTetradWord (t : Fin 14) : Fin 8 → Bit :=
  fun j => if ∃ i, icosianTetradPositions t i=j then 1 else 0

theorem icosianTetradPositions_injective (t : Fin 14) :
    Function.Injective (icosianTetradPositions t) := by
  revert t; decide +kernel

theorem icosianParityEncoder_exhaust (a : Fin 4 → Bit) :
    icosianParityEncoder a=0 ∨ icosianParityEncoder a=(fun _ => 1) ∨
      ∃ t : Fin 14,icosianParityEncoder a=icosianTetradWord t := by
  revert a; decide +kernel

theorem icosianTetradWord_mem (t : Fin 14) : icosianTetradWord t ∈ icosianParity := by
  change ∃ a,icosianParityEncoder a=icosianTetradWord t
  revert t; decide +kernel

theorem icosianParity_ones_mem : (fun _ : Fin 8 => (1 : Bit)) ∈ icosianParity := by
  change ∃ a,icosianParityEncoder a=(fun _ => 1)
  decide +kernel

end Atlas.Codes

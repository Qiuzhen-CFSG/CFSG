/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianUnitCandidates.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.IcosianParity
public import Theory.AtlasPort.Janko2.Algebra.IcosianQuaternion

/-!
# IcosianUnitCandidates

The parity code gives 240 short integer coordinate vectors, of which
120 have reduced norm one. Kernel-checked finite enumeration establishes
the candidate counts and the two possible golden norm coefficients.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianUnitCandidates.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

namespace Atlas.Algebra
open Atlas.Codes
open scoped BigOperators

abbrev IcosianIntegerCoordinates := Fin 8 → ℤ

def icosianCoordinateSign (b : Bit) : ℤ := if b=0 then 1 else -1

def icosianAxisCoordinates (p : Fin 8 × Bit) : IcosianIntegerCoordinates :=
  fun j => if j=p.1 then 2*icosianCoordinateSign p.2 else 0

def icosianTetradCoordinates (p : Fin 14 × (Fin 4 → Bit)) : IcosianIntegerCoordinates :=
  fun j => ∑ i,if j=icosianTetradPositions p.1 i then icosianCoordinateSign (p.2 i) else 0

def icosianShortCoordinates : Finset IcosianIntegerCoordinates :=
  Finset.univ.image icosianAxisCoordinates ∪ Finset.univ.image icosianTetradCoordinates

def icosianCoordinateNorm (v : IcosianIntegerCoordinates) : ℤ := ∑ i,v i^2

def icosianCoordinateTau (v : IcosianIntegerCoordinates) : ℤ :=
  2*v 0*v 1+v 1^2+2*v 2*v 3+v 3^2+2*v 4*v 5+v 5^2+2*v 6*v 7+v 7^2

def icosianNormOneCoordinates : Finset IcosianIntegerCoordinates :=
  icosianShortCoordinates.filter (fun v => icosianCoordinateTau v=0)

theorem icosianShortCoordinates_card : icosianShortCoordinates.card=240 := by
  decide +kernel

theorem icosianNormOneCoordinates_card : icosianNormOneCoordinates.card=120 := by
  decide +kernel

theorem icosianShortCoordinates_norm :
    ∀ v ∈ icosianShortCoordinates,icosianCoordinateNorm v=4 := by
  decide +kernel

theorem icosianShortCoordinates_tau :
    ∀ v ∈ icosianShortCoordinates,icosianCoordinateTau v=0 ∨ icosianCoordinateTau v=4 := by
  decide +kernel

end Atlas.Algebra

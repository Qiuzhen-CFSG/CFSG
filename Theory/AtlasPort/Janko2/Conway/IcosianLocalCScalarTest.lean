/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianLocalCScalarTest.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootLocalReferences
public import Theory.AtlasPort.Janko2.Algebra.IcosianIntegralCheck

/-!
# IcosianLocalCScalarTest

Explicit quaternionic candidate matrices define the scalar test for the shape-C
stabilizer. Finite enumeration counts the admissible scalars.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianLocalCScalarTest.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes

/-- Explicit reduction of the candidate recovered from the rational basis
coordinates; no choice of integral coefficients occurs in this expression. -/
def icosianCandidateMatrix (x : IcosianQuaternion) : IcosianMatrix :=
  icosianMatrixFromCoefficients (fun i => goldenModuloTwo
    (goldenNumerator (icosianBasisCoefficients x i)))

theorem icosianCandidateMatrix_eq (x : IcosianQuaternion) :
    icosianCandidateMatrix x=icosianModuloTwo (icosianIntegralCandidate x) :=
  (icosianModuloTwo_synthesis _).symm

def icosianLocalCConjugate (u : IcosianQuaternion) : IcosianQuaternion :=
  (1/2 : ℚ) • (icosianLocalCScalar.val*u*star icosianLocalCScalar.val)

def IcosianLocalCScalarTest (v : IcosianIntegerCoordinates) : Prop :=
  let u := icosianCoordinatesQuaternion v
  let z := icosianLocalCConjugate u
  let a := icosianCandidateMatrix u
  let b := icosianCandidateMatrix z
  IcosianIntegralTest z ∧ a 1 0=0 ∧
    b 0 0=a 0 0 ∧ b 1 1=a 1 1 ∧ b 1 0=0 ∧ b 0 1=0

instance (v : IcosianIntegerCoordinates) : Decidable (IcosianLocalCScalarTest v) :=
  inferInstanceAs (Decidable (let u := icosianCoordinatesQuaternion v
    let z := icosianLocalCConjugate u
    let a := icosianCandidateMatrix u
    let b := icosianCandidateMatrix z
    IcosianIntegralTest z ∧ a 1 0=0 ∧
      b 0 0=a 0 0 ∧ b 1 1=a 1 1 ∧ b 1 0=0 ∧ b 0 1=0))

def icosianLocalCScalarCandidates : Finset IcosianIntegerCoordinates :=
  icosianNormOneCoordinates.filter IcosianLocalCScalarTest

/-- The bounded scalar calculation concerns only the actual120 integral units,
not an ambient root or permutation representation. -/
theorem icosianLocalCScalarCandidates_card : icosianLocalCScalarCandidates.card=6 := by
  decide +kernel

end Atlas.Conway

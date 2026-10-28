/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianParityIntegral.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianOrderParity

/-!
# IcosianParityIntegral

Every integer vector allowed by the parity code gives an integral
icosian after division by two. Explicit inverse basis numerators are even,
so division yields golden-integral coefficients.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianParityIntegral.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

namespace Atlas.Algebra
open Atlas.Codes Matrix
open scoped QuadraticAlgebra

/-- The four half-integral inverse basis numerators. -/
def icosianParityNumerators {R : Type*} [Ring R] (v : Fin 8 → R) : Fin 4 → R :=
  ![v 0+v 6-v 7+2*v 4-v 5,v 1-v 6-v 4+v 5,
    v 2+2*v 6-v 7-v 4+v 5,v 3+v 7-v 6+v 4]

theorem icosianParityNumerators_encoder :
    ∀ a : Fin 4 → Bit,icosianParityNumerators (icosianParityEncoder a)=0 := by
  decide +kernel

theorem icosianParityNumerators_even (v : IcosianIntegerCoordinates)
    (hv : (fun i => (v i : Bit)) ∈ icosianParity) (j : Fin 4) :
    (2 : ℤ) ∣ icosianParityNumerators v j := by
  obtain ⟨a,ha⟩ := hv
  have hz := congrFun (icosianParityNumerators_encoder a) j
  rw [ha] at hz
  change icosianParityNumerators (fun i => (v i : Bit)) j=0 at hz
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
  convert hz using 1
  fin_cases j <;> simp [icosianParityNumerators,Matrix.cons_val_two,Matrix.cons_val_three]

def icosianParityIntegralCoefficients (v : IcosianIntegerCoordinates) : Fin 4 → GoldenInteger :=
  ![⟨icosianParityNumerators v 0/2,icosianParityNumerators v 1/2⟩,
    ⟨icosianParityNumerators v 2/2,icosianParityNumerators v 3/2⟩,
    ⟨-v 6+v 7,v 6⟩,⟨v 4-v 5,-v 4⟩]

theorem icosianParityIntegral_double (v : IcosianIntegerCoordinates)
    (hv : (fun i => (v i : Bit)) ∈ icosianParity) :
    icosianIntegralDouble (icosianParityIntegralCoefficients v)=v := by
  have h0 := Int.mul_ediv_cancel' (icosianParityNumerators_even v hv 0)
  have h1 := Int.mul_ediv_cancel' (icosianParityNumerators_even v hv 1)
  have h2 := Int.mul_ediv_cancel' (icosianParityNumerators_even v hv 2)
  have h3 := Int.mul_ediv_cancel' (icosianParityNumerators_even v hv 3)
  dsimp [icosianParityNumerators] at h0 h1 h2 h3
  funext i
  fin_cases i <;> dsimp [icosianIntegralDouble,icosianParityIntegralCoefficients,
    icosianParityNumerators]
  · linear_combination h0
  · linear_combination h1
  · linear_combination h2
  · linear_combination h3
  · ring
  · ring
  · ring

theorem icosianParityIntegral_synthesis (v : IcosianIntegerCoordinates)
    (hv : (fun i => (v i : Bit)) ∈ icosianParity) :
    icosianBasisSynthesis (fun i => goldenIntegerToRational
      (icosianParityIntegralCoefficients v i)) = icosianCoordinatesQuaternion v := by
  rw [← icosianIntegralDouble_synthesis,icosianParityIntegral_double v hv]

/-- Every parity-allowed integer coordinate vector is an actual integral
icosian, by explicit inverse basis coefficients. -/
theorem isIcosian_coordinates_of_parity (v : IcosianIntegerCoordinates)
    (hv : (fun i => (v i : Bit)) ∈ icosianParity) :
    IsIcosian (icosianCoordinatesQuaternion v) := by
  apply (isIcosian_iff_synthesis _).mpr
  refine ⟨icosianParityIntegralCoefficients v,?_⟩
  rw [← icosianIntegralDouble_synthesis,icosianParityIntegral_double v hv]

end Atlas.Algebra

/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianGoldenUnits.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianUnitNormShells
public import Theory.AtlasPort.Janko2.Algebra.IcosianModuloTwoCoordinates

/-!
# IcosianGoldenUnits

Golden-integer scalars embed in the integral order; the golden ratio
and its conjugate give explicit units. Their quaternion norms are
squares, and reduction gives scalar matrices.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianGoldenUnits.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

noncomputable section
namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra Matrix

def icosianGoldenToOrder : GoldenInteger →+* icosianOrder where
  toFun a := ⟨(goldenIntegerToRational a : IcosianQuaternion),by
    change (goldenIntegerToRational a : IcosianQuaternion)∈icosianOrder
    rw [icosianOrder_eq_generated]
    exact icosianGoldenInteger_mem_generated a⟩
  map_zero' := by apply Subtype.ext; simp
  map_one' := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp

def goldenTauUnit : GoldenIntegerˣ where
  val := QuadraticAlgebra.omega
  inv := QuadraticAlgebra.omega-1
  val_inv := by ext <;> norm_num [QuadraticAlgebra.omega]
  inv_val := by ext <;> norm_num [QuadraticAlgebra.omega]

def goldenSigmaUnit : GoldenIntegerˣ where
  val := 1-QuadraticAlgebra.omega
  inv := -QuadraticAlgebra.omega
  val_inv := by ext <;> norm_num [QuadraticAlgebra.omega]
  inv_val := by ext <;> norm_num [QuadraticAlgebra.omega]

def icosianTauUnit : icosianOrderˣ := Units.map icosianGoldenToOrder.toMonoidHom goldenTauUnit

def icosianSigmaUnit : icosianOrderˣ := Units.map icosianGoldenToOrder.toMonoidHom goldenSigmaUnit

theorem icosianGoldenToOrder_norm (a : GoldenInteger) :
    icosianNorm (icosianGoldenToOrder a).val=(goldenIntegerToRational a)^2 :=
  Quaternion.normSq_coe _

theorem icosianGoldenToOrder_integralNorm (a : GoldenInteger) :
    icosianIntegralNorm (icosianGoldenToOrder a)=a^2 := by
  apply goldenIntegerToRational_injective
  rw [icosianIntegralNorm_spec,icosianGoldenToOrder_norm,map_pow]

theorem icosianTauUnit_norm : icosianNorm (icosianTauUnit : icosianOrder).val=goldenTau^2 := by
  apply icosianGoldenToOrder_norm

theorem icosianSigmaUnit_norm : icosianNorm (icosianSigmaUnit : icosianOrder).val=goldenSigma^2 := by
  change icosianNorm (icosianGoldenToOrder (1-QuadraticAlgebra.omega)).val=(1-goldenTau)^2
  rw [icosianGoldenToOrder_norm,map_sub,map_one]
  rfl

theorem icosianGoldenToOrder_synthesis (a : GoldenInteger) :
    icosianGoldenToOrder a=icosianIntegralSynthesis ![a,0,0,0] := by
  apply Subtype.ext
  simp [icosianGoldenToOrder,icosianIntegralSynthesis,icosianBasisSynthesis,← Quaternion.coe_mul_eq_smul]

theorem icosianGoldenToOrder_reduction (a : GoldenInteger) :
    icosianModuloTwo (icosianGoldenToOrder a)=goldenModuloTwo a • (1 : IcosianMatrix) := by
  rw [icosianGoldenToOrder_synthesis,icosianModuloTwo_synthesis]
  funext i j
  fin_cases i <;> fin_cases j <;> simp [icosianMatrixFromCoefficients]

end Atlas.Algebra

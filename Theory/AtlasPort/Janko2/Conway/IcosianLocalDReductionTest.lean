/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianLocalDReductionTest.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianUpperUnitCount

/-!
# IcosianLocalDReductionTest

Explicit matrices over the four-element field encode the shape-D reduction test.
Matrix inverses and parameter equivalences count the admissible lifts.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianLocalDReductionTest.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes

def icosianLocalDMatrix (i : Fin 3) : IcosianMatrix :=
  !![![1+QuadraticAlgebra.omega,1,QuadraticAlgebra.omega] i,0;
     0,1+QuadraticAlgebra.omega]

theorem icosianLocalDMatrix_reduction (i : Fin 3) :
    icosianModuloTwo (icosianLocalDRoot.val i)=icosianLocalDMatrix i := by
  rw [show icosianLocalDRoot.val i=icosianIntegralSynthesis
    (icosianParityIntegralCoefficients (icosianReflectionDiagonalRootData 0 i)) from rfl,
    icosianModuloTwo_synthesis]
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;> decide +kernel

def icosianLocalDMatrixInverse (i : Fin 3) : IcosianMatrix :=
  (Matrix.det (icosianLocalDMatrix i))^2 • Matrix.adjugate (icosianLocalDMatrix i)

theorem icosianLocalDMatrix_mul_inverse (i : Fin 3) :
    icosianLocalDMatrix i*icosianLocalDMatrixInverse i=1 := by
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;> decide +kernel

def icosianLocalDMatrixConjugate (a : IcosianSpecialLinear) (i : Fin 3) : IcosianMatrix :=
  icosianLocalDMatrix i*(a : IcosianMatrix)*icosianLocalDMatrixInverse i

def IcosianLocalDReductionTest (a : IcosianSpecialLinear) : Prop :=
  let b := icosianLocalDMatrixConjugate a
  (∀ i,b i 1 0=0) ∧ (∀ i,b i 0 0=b 2 0 0) ∧ (∀ i,b i 1 1=b 2 1 1) ∧
    b 0 0 1+b 1 0 1+b 2 0 1=0

instance (a : IcosianSpecialLinear) : Decidable (IcosianLocalDReductionTest a) :=
  inferInstanceAs (Decidable (let b := icosianLocalDMatrixConjugate a
    (∀ i,b i 1 0=0) ∧ (∀ i,b i 0 0=b 2 0 0) ∧ (∀ i,b i 1 1=b 2 1 1) ∧
      b 0 0 1+b 1 0 1+b 2 0 1=0))

abbrev IcosianLocalDReductionParameters := {a : IcosianSpecialLinear // IcosianLocalDReductionTest a}

theorem icosianLocalDReductionTest_iff : ∀ a : IcosianSpecialLinear,
    IcosianLocalDReductionTest a ↔ a 1 0=0 := by
  decide +kernel

/-- The scalar reductions are precisely an actual Borel subgroup of SL2(F4). -/

theorem icosianLocalDReductionParameters_card : Nat.card IcosianLocalDReductionParameters=12 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight icosianLocalDReductionTest_iff)]
  exact icosianUpperSL2_card

abbrev IcosianLocalDUnitParameters :=
  {u : icosianNormOneGroup // IcosianLocalDReductionTest (icosianNormOneReduction u)}

def icosianLocalDUnitParametersEquiv : IcosianLocalDUnitParameters ≃
    IcosianLocalDReductionParameters × icosianNormOneReduction.ker :=
  (icosianNormOneReductionCoordinates.subtypeEquiv (fun u => by
    rw [icosianNormOneReductionCoordinates_fst u])).trans
      Equiv.prodSubtypeFstEquivSubtypeProd

theorem icosianLocalDUnitParameters_card : Nat.card IcosianLocalDUnitParameters=24 := by
  rw [Nat.card_congr icosianLocalDUnitParametersEquiv,Nat.card_prod,
    icosianLocalDReductionParameters_card,icosianNormOneReduction_kernel_card]

end Atlas.Conway

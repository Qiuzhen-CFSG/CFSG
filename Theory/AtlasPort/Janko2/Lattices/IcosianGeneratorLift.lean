/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianGeneratorLift.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianGeneratorFreeData

/-!
# Icosian Generator Lift

An integral linear combination of the twelve glue rows lifts each
six-coordinate glue word. The information-coordinate identities verify
the lift and its membership in any submodule containing those rows.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianGeneratorLift.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped Matrix QuadraticAlgebra BigOperators
attribute [local irreducible] icosianComparisonSourceData

/-- Six information coefficients for the reduced congruence module. -/
def icosianGlueFreePart {R : Type*} (a : Fin 3 → Fin 4 → R) : Fin 6 → R :=
  ![a 1 1,a 1 3,a 2 0,a 2 1,a 2 2,a 2 3]

def icosianGlueBinaryParameter (a : Fin 6 → GoldenFour) (k : Fin 12) : ℤ :=
  if k.val % 2=0 then ((a ⟨k.val/2,by omega⟩).re.val : ℤ)
  else ((a ⟨k.val/2,by omega⟩).im.val : ℤ)

def icosianGlueLiftCoefficients (a : Fin 6 → GoldenFour) : Fin 3 → Fin 4 → GoldenInteger :=
  ∑ k : Fin 12,icosianGlueBinaryParameter a k •
    icosianComparisonSourceCoefficients (icosianGlueRowIndex k)

theorem icosianGlueLift_free (a : Fin 6 → GoldenFour) :
    icosianGlueFreePart (fun i j => goldenModuloTwo (icosianGlueLiftCoefficients a i j))=a := by
  have hread (l : Fin 12) : (∑ k : Fin 12,icosianGlueBinaryParameter a k *
      icosianComparisonSourceData (icosianGlueRowIndex k) (icosianGlueFreePosition l))=
      icosianGlueBinaryParameter a l := by
    simp_rw [icosianGlueRows_free]
    simp
  have hre (i : Fin 3) (j : Fin 4) : (icosianGlueLiftCoefficients a i j).re=
      ∑ k : Fin 12,icosianGlueBinaryParameter a k *
        icosianComparisonSourceData (icosianGlueRowIndex k) (icosianRealCoordinateIndex (i,j,0)) := by
    change QuadraticAlgebra.reₗ (1 : ℤ) 1
      ((∑ k : Fin 12,icosianGlueBinaryParameter a k •
        icosianComparisonSourceCoefficients (icosianGlueRowIndex k)) i j)=_
    simp only [Finset.sum_apply,Pi.smul_apply,map_sum,map_smul]
    rfl
  have him (i : Fin 3) (j : Fin 4) : (icosianGlueLiftCoefficients a i j).im=
      ∑ k : Fin 12,icosianGlueBinaryParameter a k *
        icosianComparisonSourceData (icosianGlueRowIndex k) (icosianRealCoordinateIndex (i,j,1)) := by
    change QuadraticAlgebra.imₗ (1 : ℤ) 1
      ((∑ k : Fin 12,icosianGlueBinaryParameter a k •
        icosianComparisonSourceCoefficients (icosianGlueRowIndex k)) i j)=_
    simp only [Finset.sum_apply,Pi.smul_apply,map_sum,map_smul]
    rfl
  funext l
  fin_cases l <;> ext
  · change ((icosianGlueLiftCoefficients a 1 1).re : Bit)=(a 0).re
    rw [hre]
    change (((∑ k : Fin 12,icosianGlueBinaryParameter a k *
      icosianComparisonSourceData (icosianGlueRowIndex k) (icosianGlueFreePosition 0)) : ℤ) : Bit)=(a 0).re
    rw [hread]
    simp [icosianGlueBinaryParameter]
  · change ((icosianGlueLiftCoefficients a 1 1).im : Bit)=(a 0).im
    rw [him]
    change (((∑ k : Fin 12,icosianGlueBinaryParameter a k *
      icosianComparisonSourceData (icosianGlueRowIndex k) (icosianGlueFreePosition 1)) : ℤ) : Bit)=(a 0).im
    rw [hread]
    simp [icosianGlueBinaryParameter]
  · change ((icosianGlueLiftCoefficients a 1 3).re : Bit)=(a 1).re
    rw [hre]
    change (((∑ k : Fin 12,icosianGlueBinaryParameter a k *
      icosianComparisonSourceData (icosianGlueRowIndex k) (icosianGlueFreePosition 2)) : ℤ) : Bit)=(a 1).re
    rw [hread]
    simp [icosianGlueBinaryParameter]
  · change ((icosianGlueLiftCoefficients a 1 3).im : Bit)=(a 1).im
    rw [him]
    change (((∑ k : Fin 12,icosianGlueBinaryParameter a k *
      icosianComparisonSourceData (icosianGlueRowIndex k) (icosianGlueFreePosition 3)) : ℤ) : Bit)=(a 1).im
    rw [hread]
    simp [icosianGlueBinaryParameter]
  · change ((icosianGlueLiftCoefficients a 2 0).re : Bit)=(a 2).re
    rw [hre]
    change (((∑ k : Fin 12,icosianGlueBinaryParameter a k *
      icosianComparisonSourceData (icosianGlueRowIndex k) (icosianGlueFreePosition 4)) : ℤ) : Bit)=(a 2).re
    rw [hread]
    simp [icosianGlueBinaryParameter]
  · change ((icosianGlueLiftCoefficients a 2 0).im : Bit)=(a 2).im
    rw [him]
    change (((∑ k : Fin 12,icosianGlueBinaryParameter a k *
      icosianComparisonSourceData (icosianGlueRowIndex k) (icosianGlueFreePosition 5)) : ℤ) : Bit)=(a 2).im
    rw [hread]
    simp [icosianGlueBinaryParameter]
  · change ((icosianGlueLiftCoefficients a 2 1).re : Bit)=(a 3).re
    rw [hre]
    change (((∑ k : Fin 12,icosianGlueBinaryParameter a k *
      icosianComparisonSourceData (icosianGlueRowIndex k) (icosianGlueFreePosition 6)) : ℤ) : Bit)=(a 3).re
    rw [hread]
    simp [icosianGlueBinaryParameter]
  · change ((icosianGlueLiftCoefficients a 2 1).im : Bit)=(a 3).im
    rw [him]
    change (((∑ k : Fin 12,icosianGlueBinaryParameter a k *
      icosianComparisonSourceData (icosianGlueRowIndex k) (icosianGlueFreePosition 7)) : ℤ) : Bit)=(a 3).im
    rw [hread]
    simp [icosianGlueBinaryParameter]
  · change ((icosianGlueLiftCoefficients a 2 2).re : Bit)=(a 4).re
    rw [hre]
    change (((∑ k : Fin 12,icosianGlueBinaryParameter a k *
      icosianComparisonSourceData (icosianGlueRowIndex k) (icosianGlueFreePosition 8)) : ℤ) : Bit)=(a 4).re
    rw [hread]
    simp [icosianGlueBinaryParameter]
  · change ((icosianGlueLiftCoefficients a 2 2).im : Bit)=(a 4).im
    rw [him]
    change (((∑ k : Fin 12,icosianGlueBinaryParameter a k *
      icosianComparisonSourceData (icosianGlueRowIndex k) (icosianGlueFreePosition 9)) : ℤ) : Bit)=(a 4).im
    rw [hread]
    simp [icosianGlueBinaryParameter]
  · change ((icosianGlueLiftCoefficients a 2 3).re : Bit)=(a 5).re
    rw [hre]
    change (((∑ k : Fin 12,icosianGlueBinaryParameter a k *
      icosianComparisonSourceData (icosianGlueRowIndex k) (icosianGlueFreePosition 10)) : ℤ) : Bit)=(a 5).re
    rw [hread]
    simp [icosianGlueBinaryParameter]
  · change ((icosianGlueLiftCoefficients a 2 3).im : Bit)=(a 5).im
    rw [him]
    change (((∑ k : Fin 12,icosianGlueBinaryParameter a k *
      icosianComparisonSourceData (icosianGlueRowIndex k) (icosianGlueFreePosition 11)) : ℤ) : Bit)=(a 5).im
    rw [hread]
    simp [icosianGlueBinaryParameter]

noncomputable def icosianGlueLift (a : Fin 6 → GoldenFour) : IcosianCoordinates :=
  ∑ k : Fin 12,icosianGlueBinaryParameter a k •
    icosianComparisonSourceGenerator (icosianGlueRowIndex k)

theorem icosianGlueLift_integralCoefficients (a : Fin 6 → GoldenFour) (i : Fin 3) :
    icosianIntegralCoefficients (icosianGlueLift a i)=icosianGlueLiftCoefficients a i := by
  change icosianIntegralLinearEquiv (icosianGlueLift a i)=_
  simp only [icosianGlueLift,Finset.sum_apply,Pi.smul_apply,map_sum,map_smul]
  change (∑ k : Fin 12,icosianGlueBinaryParameter a k •
    icosianIntegralEquiv (icosianIntegralSynthesis
      (icosianComparisonSourceCoefficients (icosianGlueRowIndex k) i)))=_
  have hs (b : Fin 4 → GoldenInteger) :
      icosianIntegralEquiv (icosianIntegralSynthesis b)=b :=
    icosianIntegralEquiv.apply_symm_apply b
  simp only [hs]
  rfl

theorem icosianGlueLift_mem (S : Submodule ℤ IcosianCoordinates)
    (hS : ∀ k : Fin 12,icosianComparisonSourceGenerator (icosianGlueRowIndex k)∈S)
    (a : Fin 6 → GoldenFour) : icosianGlueLift a∈S := by
  exact S.sum_mem (fun k _ => S.smul_mem _ (hS k))

end Atlas.Lattices

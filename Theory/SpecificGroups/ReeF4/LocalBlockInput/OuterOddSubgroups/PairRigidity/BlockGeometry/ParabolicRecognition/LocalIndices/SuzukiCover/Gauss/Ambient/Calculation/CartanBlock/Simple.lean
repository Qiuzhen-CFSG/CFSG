module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss.Ambient.Calculation.Blocks
/-!
# Simple root entries on the Cartan block

These four matrices retain all four Cartan columns and the eight middle B₂
root coordinates. The proofs compare every entry directly with the linear and
quadratic supports in `Ambient.Tables`. They are the starting point for the
literal Weyl and four-root word calculation, including arbitrary parameters.

Source: GLS3, Table 2.4 type V and 2.3.4--8;
`refs/KGroup/GLS3/chapter2.tex` and `Ambient.Tables`.
-/

namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation
namespace CartanBlock
open BlockParameters.FieldRecovery
open scoped Matrix
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
variable {m : ℕ}

def simple_true_0 (t : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,t,0,0,0,0,0;
      0,0,1,0,0,0,0,0,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,0,1,0,0,0,0,0,0;
      0,0,0,0,0,0,1,0,0,0,0,0;
      0,0,0,0,0,t,0,1,0,0,0,0;
      0,0,0,0,0,0,0,0,1,0,0,0;
      t,0,0,0,0,0,t ^ 2,0,0,1,0,0;
      0,0,0,0,0,0,0,0,t,0,1,0;
      0,0,0,0,0,0,0,0,0,0,0,1]

lemma simple_true_0_eq (t : CoefficientField m) :
    blockSimple 0 true 0 t = simple_true_0 t := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [blockSimple, blockCoord, simpleMatrix, simpleIndex, incidence,
      linearSupport, quadraticSupport, simple_true_0]

def simple_true_1 (t : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,0,0,0,0,0,0;
      0,0,1,0,0,0,0,t,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,t,1,0,0,0,0,0,0;
      0,0,0,0,t ^ 2,0,1,0,0,0,0,0;
      0,0,0,0,0,0,0,1,0,0,0,0;
      0,t,0,t,0,0,0,t ^ 2,1,0,0,0;
      0,0,0,0,0,0,0,0,0,1,0,0;
      0,0,0,0,0,0,0,0,0,t,1,0;
      0,0,0,0,0,0,0,0,0,t ^ 2,0,1]

lemma simple_true_1_eq (t : CoefficientField m) :
    blockSimple 0 true 1 t = simple_true_1 t := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [blockSimple, blockCoord, simpleMatrix, simpleIndex, incidence,
      linearSupport, quadraticSupport, simple_true_1]

def simple_false_0 (t : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,0,0,0,t,0,0;
      0,0,1,0,0,0,0,0,0,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,0,0,0,0,0,0;
      0,0,0,0,0,1,0,t,0,0,0,0;
      t,0,0,0,0,0,1,0,0,t ^ 2,0,0;
      0,0,0,0,0,0,0,1,0,0,0,0;
      0,0,0,0,0,0,0,0,1,0,t,0;
      0,0,0,0,0,0,0,0,0,1,0,0;
      0,0,0,0,0,0,0,0,0,0,1,0;
      0,0,0,0,0,0,0,0,0,0,0,1]

lemma simple_false_0_eq (t : CoefficientField m) :
    blockSimple 0 false 0 t = simple_false_0 t := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [blockSimple, blockCoord, simpleMatrix, simpleIndex, incidence,
      linearSupport, quadraticSupport, simple_false_0]

def simple_false_1 (t : CoefficientField m) : Matrix (Fin 12) (Fin 12) (CoefficientField m) :=
  !![1,0,0,0,0,0,0,0,0,0,0,0;
      0,1,0,0,0,0,0,0,0,0,0,0;
      0,0,1,0,0,0,0,0,t,0,0,0;
      0,0,0,1,0,0,0,0,0,0,0,0;
      0,0,0,0,1,0,t ^ 2,0,0,0,0,0;
      0,0,0,0,0,1,t,0,0,0,0,0;
      0,0,0,0,0,0,1,0,0,0,0,0;
      0,t,0,t,0,0,0,1,t ^ 2,0,0,0;
      0,0,0,0,0,0,0,0,1,0,0,0;
      0,0,0,0,0,0,0,0,0,1,0,t ^ 2;
      0,0,0,0,0,0,0,0,0,0,1,t;
      0,0,0,0,0,0,0,0,0,0,0,1]

lemma simple_false_1_eq (t : CoefficientField m) :
    blockSimple 0 false 1 t = simple_false_1 t := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [blockSimple, blockCoord, simpleMatrix, simpleIndex, incidence,
      linearSupport, quadraticSupport, simple_false_1]

end
end CartanBlock
end ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData.Ambient.Calculation

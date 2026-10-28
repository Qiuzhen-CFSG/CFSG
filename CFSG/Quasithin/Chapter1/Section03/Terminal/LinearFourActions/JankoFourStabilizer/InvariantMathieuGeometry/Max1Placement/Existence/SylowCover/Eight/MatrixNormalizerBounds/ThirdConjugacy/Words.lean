module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4Transport
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.KernelMasks

/-!
# Actual ambient words for the third-eight comparison

The word first moves the max4 seed to kernel mask 1453, then uses a
short ambient word and a second sixth power. Its definition is unconditional;
the separate matrix certificates prove its effect on all eight elements.

The kernel masks use the already certified ATLAS max1 basis. The max4 seed
uses the literal ATLAS max4 program. See ThirdConjugacy/source/README.md.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
open Subgroup Janko4 Janko4.Cardinality
open Janko4.Simplicity.Max1Fusion.KernelOrbits
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

theorem kernelMask_zero : kernelMask 0 = 1 := by
  simp only [kernelMask, maskValue_zero, map_one]

theorem kernelMask_xor (m n : ℕ) :
    kernelMask (Nat.xor m n) = kernelMask m * kernelMask n := by
  simp only [kernelMask, maskValue_xor, map_mul]

theorem kernelMask_basis (i : Fin 11) :
    kernelMask (2 ^ i.val) = (KernelCount.basis matrixA_mul_self matrixB_pow_four i : Model) := by
  change ((maskValue matrixA_mul_self matrixB_pow_four (2 ^ i.val) :
    max1Subgroup matrixA_mul_self matrixB_pow_four) : Model) = _
  rw [maskValue_basis]

def firstProduct : Model := (Janko4.LocalStructure.SymmetricLinear.NormalEight.seed : Model) * kernelMask 1453

def firstSquare : Model := firstProduct * firstProduct

def firstCube : Model := firstSquare * firstProduct

def firstConjugator : Model := firstCube * firstCube

def bInverse : Model := (b)⁻¹

def ambientWord1 : Model := a * bInverse

def ambientWord2 : Model := ambientWord1 * bInverse

def ambientWord3 : Model := ambientWord2 * a

def ambientWord4 : Model := ambientWord3 * b

def ambientWord5 : Model := ambientWord4 * b

def ambientWord6 : Model := ambientWord5 * b

def ambientWord7 : Model := ambientWord6 * a

def ambientWord8 : Model := ambientWord7 * bInverse

def ambientWord9 : Model := ambientWord8 * a

def ambientWord10 : Model := ambientWord9 * bInverse

def ambientWord11 : Model := ambientWord10 * a

def ambientWord12 : Model := ambientWord11 * bInverse

def ambientWord13 : Model := ambientWord12 * a

def ambientWord14 : Model := ambientWord13 * bInverse

def ambientInverse : Model := (ambientWord14)⁻¹

def secondLeft : Model := ambientInverse * kernelMask 1453

def secondConjugate : Model := secondLeft * ambientWord14

def secondProduct : Model := secondConjugate * kernelMask 1453

def secondSquare : Model := secondProduct * secondProduct

def secondCube : Model := secondSquare * secondProduct

def secondSixth : Model := secondCube * secondCube

def centralizerWord : Model := ambientWord14 * secondSixth

def rightConjugator : Model := firstConjugator * centralizerWord

/-- The requested left conjugation uses the inverse of the computed right conjugator. -/
def conjugator : Model := rightConjugator⁻¹

/-- Ascending XOR coordinates for the third prescribed row. -/
def targetMask : Fin 8 → ℕ := ![0, 571, 1387, 1872, 198, 765, 1453, 1942]

def targetElement (i : Fin 8) : Model := kernelMask (targetMask i)

def targetEight : Subgroup Model := closure {kernelMask 571, kernelMask 1387, kernelMask 198}

/-- The checked conjugator has this permutation of the eight listed words. -/
def imageIndex : Fin 8 → Fin 8 := ![0, 6, 2, 3, 5, 4, 1, 7]

theorem targetElement_mem (i : Fin 8) : targetElement i ∈ targetEight := by
  have h1 : kernelMask 571 ∈ targetEight := subset_closure (by simp)
  have h2 : kernelMask 1387 ∈ targetEight := subset_closure (by simp)
  have h4 : kernelMask 198 ∈ targetEight := subset_closure (by simp)
  have h3 : kernelMask 1872 ∈ targetEight := by
    rw [show kernelMask 1872 = kernelMask 571 * kernelMask 1387 from kernelMask_xor 571 1387]
    exact mul_mem h1 h2
  fin_cases i
  · change kernelMask 0 ∈ targetEight
    rw [kernelMask_zero]
    exact targetEight.one_mem
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · change kernelMask 765 ∈ targetEight
    rw [show kernelMask 765 = kernelMask 571 * kernelMask 198 from kernelMask_xor 571 198]
    exact mul_mem h1 h4
  · change kernelMask 1453 ∈ targetEight
    rw [show kernelMask 1453 = kernelMask 1387 * kernelMask 198 from kernelMask_xor 1387 198]
    exact mul_mem h2 h4
  · change kernelMask 1942 ∈ targetEight
    rw [show kernelMask 1942 = kernelMask 1872 * kernelMask 198 from kernelMask_xor 1872 198]
    exact mul_mem h3 h4

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy

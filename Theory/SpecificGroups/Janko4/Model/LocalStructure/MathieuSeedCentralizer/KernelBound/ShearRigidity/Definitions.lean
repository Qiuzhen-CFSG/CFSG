module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.Data
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.FormConstraints

/-!
# The concrete spaces and two tests for pointwise shear rigidity

The mixed generators are the proposed complete mixed image. The candidate
shears are their images under the displayed inverse of the first restriction.
Neither definition asserts completeness. The two test forms are decoded in
the original ATLAS coordinates before applying the shared change of basis.

Source: `source/README.md`, the reproduced `kernel-linear.json`, and the actual
exterior generators in `KernelEquations.ExteriorSpace`.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity
open Coordinates GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

def rowsHalf (rows : Vector ℕ 56) : HalfMatrix := fun i j => bit (rows.get i) j.val

def mixedBasis (i : Fin 616) : HalfMatrix := decodeHalf (mixedWords.get i)

def mixedSpan : Submodule (ZMod 2) HalfMatrix :=
  Submodule.span (ZMod 2) (Set.range mixedBasis)

def testRestriction (t : Fin 2) : HalfMatrix :=
  rowsHalf (if t = 0 then r0Rows else r1Rows)

def inverseRestriction : HalfMatrix := rowsHalf r0InverseRows

def extraShear : HalfMatrix := rowsHalf extraShearRows

def candidateBasis (i : Fin 616) : HalfMatrix := inverseRestriction * mixedBasis i

def candidateSpan : Submodule (ZMod 2) HalfMatrix :=
  Submodule.span (ZMod 2) (Set.range candidateBasis)

def testForm (t : Fin 2) : BlockMatrix :=
  formCoordinates (decodeExteriorForm (testFormWords.get t))

/-- A four-entry functional separating the extra shear after the second test. -/
def separatingFunctional : HalfMatrix →ₗ[ZMod 2] ZMod 2 where
  toFun X := X 4 47 + X 47 4 + X 54 55 + X 55 54
  map_add' X Y := by simp only [Matrix.add_apply]; ring
  map_smul' a X := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity

module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Encoding
public import Theory.SpecificGroups.PSL3Three.FiniteModel

/-!
# A finite right-edge certificate on the actual native matrices

An `EdgeTable` assigns encoded matrices to the native base-three matrix codes.
It is normalized at the identity and respects right multiplication by the two
specified ATLAS generators on every determinant-one code. It assumes neither
a presentation nor a homomorphism. `Transport` proves that these finite data
supply the required marked action of the literal projective quotient.

The witness remains a separate finite-certificate obligation. The native
encoding is `Matrix.PSL3Three.FiniteModel`; numerical attribution is in `Data`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction

/-- Finite data required to interpret the marked matrices. This does not assume
any group law for the encoded image matrices. -/
structure EdgeTable where
  image : Matrix.PSL3Three.MatrixCode → CodeMatrix
  one : image (Matrix.PSL3Three.matrixCodeEquiv 1) = matrixOne
  rightA : ∀ c, Matrix.PSL3Three.codeDet c = 1 →
    image (Matrix.PSL3Three.matrixCodeEquiv
      (Matrix.PSL3Three.decodeMatrix c * nativeA.val)) = matrixMul (image c) codesA
  rightB : ∀ c, Matrix.PSL3Three.codeDet c = 1 →
    image (Matrix.PSL3Three.matrixCodeEquiv
      (Matrix.PSL3Three.decodeMatrix c * nativeB.val)) = matrixMul (image c) codesB

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction

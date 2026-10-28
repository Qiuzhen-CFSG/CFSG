module
public import Theory.Representation.Mathieu.M22James.Unitary.Data
/-!
# Checked unitary coordinate certificates

The coordinate matrix sends the native central scalar to omega and the two
native generators to the six-dimensional matrices in `Data`. Both preserve
the identity Hermitian matrix. Each equality is checked on the two binary
coefficients separately, avoiding costly reduction of field equality proofs.

Source and ATLAS attribution: see `Data` and `M22James.Model`.
-/

@[expose] public section
set_option Elab.async false
namespace Sporadic.Mathieu.M22TripleCover.Unitary
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Matrix Representation.SL2FourNatural
open scoped Matrix
theorem coord_scalar : coordMatrix * ((1 + matrixJ).map (algebraMap (ZMod 2) F)) =
    (QuadraticAlgebra.omega : F) • coordMatrix := by
  ext i j <;> revert i j <;> decide +kernel

theorem coord_generatorA : coordMatrix * (matrixA.map (algebraMap (ZMod 2) F)) =
    generatorA * coordMatrix := by
  ext i j <;> revert i j <;> decide +kernel

theorem coord_generatorB : coordMatrix * (matrixB.map (algebraMap (ZMod 2) F)) =
    generatorB * coordMatrix := by
  ext i j <;> revert i j <;> decide +kernel

theorem generatorA_unitary : generatorA.transpose.map fieldFrobenius * generatorA = 1 := by
  ext i j <;> revert i j <;> decide +kernel

theorem generatorB_unitary : generatorB.transpose.map fieldFrobenius * generatorB = 1 := by
  ext i j <;> revert i j <;> decide +kernel

end Sporadic.Mathieu.M22TripleCover.Unitary

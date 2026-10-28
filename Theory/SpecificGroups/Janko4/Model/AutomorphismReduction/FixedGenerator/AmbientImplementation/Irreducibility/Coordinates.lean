module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.Irreducibility.Data
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.Irreducibility.PackedSpan
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.Products

/-!
# Coordinate certificates for the binary irreducibility test

The transposed packed generators implement column action. The test matrix
is exactly I + A + B + AB + B². Every entry is kernel checked against
the literal ATLAS data attributed in `Model/Data.lean`.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.IrreducibilityCertificate
open GeneratorCertificates Matrix

set_option maxRecDepth 10000 in
theorem transposeA_correct : decodeRows transposeA = matrixA.transpose := by
  have h : ∀ i j : Fin 112,
      (transposeA.get i).testBit j.val = (aRows.get j).testBit i.val := by decide +kernel
  funext i j
  change bit (transposeA.get i) j.val = bit (aRows.get j) i.val
  simp only [bit, h]

set_option maxRecDepth 10000 in
theorem transposeB_correct : decodeRows transposeB = matrixB.transpose := by
  have h : ∀ i j : Fin 112,
      (transposeB.get i).testBit j.val = (bRows.get j).testBit i.val := by decide +kernel
  funext i j
  change bit (transposeB.get i) j.val = bit (bRows.get j) i.val
  simp only [bit, h]

set_option maxRecDepth 10000 in
theorem testRows_correct :
    decodeRows testRows = 1 + matrixA + matrixB + matrixA * matrixB + matrixB * matrixB := by
  have h : ∀ i : Fin 112, testRows.get i =
      packedOne.get i ^^^ aRows.get i ^^^ bRows.get i ^^^ cRows.get i ^^^ b2Rows.get i := by
    simp only [packedOne, get_ofFn]
    decide +kernel
  have hm : decodeRows testRows = decodeRows packedOne + decodeRows aRows +
      decodeRows bRows + decodeRows cRows + decodeRows b2Rows := by
    funext i j
    change bit (testRows.get i) j.val = bit (packedOne.get i) j.val +
      bit (aRows.get i) j.val + bit (bRows.get i) j.val +
      bit (cRows.get i) j.val + bit (b2Rows.get i) j.val
    rw [h, bit_xor, bit_xor, bit_xor, bit_xor]
  rw [← product_a_b, ← product_b_b, decode_packedMul, decode_packedMul,
    decode_packedOne] at hm
  exact hm


end Janko4.OuterReduction.FixedGenerator.IrreducibilityCertificate

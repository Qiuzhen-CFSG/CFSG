module

public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Image.Certificates.BlockChecks0
public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Image.Certificates.BlockChecks1
public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Image.Certificates.BlockChecks2
public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Image.Certificates.BlockChecks3

/-! Assembly of the independently checked generator block certificates. -/

public section
namespace Sporadic.Mathieu.M23Geometry.PairPlaneImage

theorem generator_block_bits : ∀ t i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint t p).val =
      (m23BlockMask (generatorBlock t i)).testBit p.val := by
  intro t
  fin_cases t
  · exact generator_block_bits_0
  · exact generator_block_bits_1
  · exact generator_block_bits_2
  · exact generator_block_bits_3
  · exact generator_block_bits_4
  · exact generator_block_bits_5
  · exact generator_block_bits_6
  · exact generator_block_bits_7
  · exact generator_block_bits_8
  · exact generator_block_bits_9
  · exact generator_block_bits_10
  · exact generator_block_bits_11
  · exact generator_block_bits_12
  · exact generator_block_bits_13
  · exact generator_block_bits_14
  · exact generator_block_bits_15
  · exact generator_block_bits_16
  · exact generator_block_bits_17
  · exact generator_block_bits_18
  · exact generator_block_bits_19
  · exact generator_block_bits_20
  · exact generator_block_bits_21
  · exact generator_block_bits_22
  · exact generator_block_bits_23

end Sporadic.Mathieu.M23Geometry.PairPlaneImage

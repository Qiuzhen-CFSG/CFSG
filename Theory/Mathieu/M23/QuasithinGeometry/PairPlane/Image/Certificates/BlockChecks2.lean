module

public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Image.Certificates.Data

/-! Kernel certificates for six elementary generators on the 253 heptad masks. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

public section
namespace Sporadic.Mathieu.M23Geometry.PairPlaneImage

theorem generator_block_bits_12 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 12 p).val =
      (m23BlockMask (generatorBlock 12 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_13 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 13 p).val =
      (m23BlockMask (generatorBlock 13 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_14 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 14 p).val =
      (m23BlockMask (generatorBlock 14 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_15 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 15 p).val =
      (m23BlockMask (generatorBlock 15 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_16 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 16 p).val =
      (m23BlockMask (generatorBlock 16 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_17 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 17 p).val =
      (m23BlockMask (generatorBlock 17 i)).testBit p.val := by decide +kernel

end Sporadic.Mathieu.M23Geometry.PairPlaneImage

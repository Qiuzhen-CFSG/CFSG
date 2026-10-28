module

public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Image.Certificates.Data

/-! Kernel certificates for six elementary generators on the 253 heptad masks. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

public section
namespace Sporadic.Mathieu.M23Geometry.PairPlaneImage

theorem generator_block_bits_6 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 6 p).val =
      (m23BlockMask (generatorBlock 6 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_7 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 7 p).val =
      (m23BlockMask (generatorBlock 7 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_8 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 8 p).val =
      (m23BlockMask (generatorBlock 8 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_9 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 9 p).val =
      (m23BlockMask (generatorBlock 9 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_10 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 10 p).val =
      (m23BlockMask (generatorBlock 10 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_11 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 11 p).val =
      (m23BlockMask (generatorBlock 11 i)).testBit p.val := by decide +kernel

end Sporadic.Mathieu.M23Geometry.PairPlaneImage

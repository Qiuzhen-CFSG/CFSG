module

public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Image.Certificates.Data

/-! Kernel certificates for six elementary generators on the 253 heptad masks. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

public section
namespace Sporadic.Mathieu.M23Geometry.PairPlaneImage

theorem generator_block_bits_0 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 0 p).val =
      (m23BlockMask (generatorBlock 0 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_1 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 1 p).val =
      (m23BlockMask (generatorBlock 1 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_2 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 2 p).val =
      (m23BlockMask (generatorBlock 2 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_3 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 3 p).val =
      (m23BlockMask (generatorBlock 3 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_4 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 4 p).val =
      (m23BlockMask (generatorBlock 4 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_5 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 5 p).val =
      (m23BlockMask (generatorBlock 5 i)).testBit p.val := by decide +kernel

end Sporadic.Mathieu.M23Geometry.PairPlaneImage

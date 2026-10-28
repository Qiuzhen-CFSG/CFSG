module

public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Image.Certificates.Data

/-! Kernel certificates for six elementary generators on the 253 heptad masks. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

public section
namespace Sporadic.Mathieu.M23Geometry.PairPlaneImage

theorem generator_block_bits_18 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 18 p).val =
      (m23BlockMask (generatorBlock 18 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_19 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 19 p).val =
      (m23BlockMask (generatorBlock 19 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_20 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 20 p).val =
      (m23BlockMask (generatorBlock 20 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_21 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 21 p).val =
      (m23BlockMask (generatorBlock 21 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_22 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 22 p).val =
      (m23BlockMask (generatorBlock 22 i)).testBit p.val := by decide +kernel

theorem generator_block_bits_23 : ∀ i (p : Fin 23),
    (m23BlockMask i).testBit (generatorPoint 23 p).val =
      (m23BlockMask (generatorBlock 23 i)).testBit p.val := by decide +kernel

end Sporadic.Mathieu.M23Geometry.PairPlaneImage

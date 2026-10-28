module

public import Theory.Representation.PSL3Two.FourGroupGeometry.FixedSpaces.Certificates

/-!
# The natural fixed-space calculation for a normalized four-group

Normalize one nonidentity involution to I + E₀₂. For each independent
commuting involution, every common fixed vector is the sum of two natural
displacements. This small calculation uses the actual three-dimensional
binary matrices, with kernel-checked reduction. The parent module transports
it through the marked local conjugation action.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893, the order-greater-than-q fixed-space step.
-/

public section
open Matrix BinaryLinearThree.FourGroupGeometry.FixedSpaces
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.NaturalFour

set_option synthInstance.maxSize 256 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- A fixed natural vector is a sum of displacements by the two generators. -/
theorem normalized_fixed_displacement : ∀ b : Matrix.PSL3Two.SL,
    b ≠ 1 → b ≠ involution → b * b = 1 → b * involution = involution * b →
    ∀ w : Fin 3 → ZMod 2,
      involution.val *ᵥ w = w → b.val *ᵥ w = w →
      ∃ u v : Fin 3 → ZMod 2,
        w = (involution.val *ᵥ u - u) + (b.val *ᵥ v - v) := by decide +kernel

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.NaturalFour

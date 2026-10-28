module
public import Theory.GroupTheory.PCoreCenterEmbedding
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure

/-!
# The triality arms factor centralizes its core center

The arms radical center is the embedded center of the full unipotent
group. The arms factor centralizes it, including at the binary parameter.
The literal radical identification transfers this to the intrinsic core.

Source: Aschbacher--Smith F.1.12(I)(4), pp.262--264, and 10.2.9,
pp.750--751, with the genuine graph-field triality carrier.
-/

public section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.Parabolics
/-- The arms factor centralizes the center of its own two-core. -/
theorem arms_core_center_le_center
    (P : Triality.Standard.Parameters) (hp : P.prime = 2) :
    let B := Triality.Standard.Parabolics.localFactor P .arms
    (center (pCore 2 B)).map (pCore 2 B).subtype ≤ center B := by
  open Triality.Standard Triality.Standard.Parabolics in
  apply center_pCore_map_le_center_of_embedded (localFactor P .arms) (radical P .arms)
    (localFactor_twoCore_map P hp .arms)
  open Triality.Standard Triality.Standard.Parabolics in
  rw [RadicalCoordinates.embedded_center_radical_arms_eq_center_unipotent P hp]
  open Triality.Standard Triality.Standard.Parabolics in
  exact le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (localFactor_arms_commutator_center_unipotent P hp))

end Triality.Standard.Parabolics

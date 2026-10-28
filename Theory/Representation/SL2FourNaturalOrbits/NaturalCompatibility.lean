module
public import Theory.Representation.SL2FourNaturalOrbits.PointCommutator
public import Theory.Representation.SL2OrthogonalCover.Universal

/-!
# Compatibility of the literal natural SL₂(4) actions

The binary matrix action used for the finite cubic and residual calculations
is the scalar restriction of the field-natural action used for component
covers. The equality retains the concrete field of four elements and the
same vectors, so source consumers need no change of module marking.
-/
public section
namespace Representation.SL2FourNatural

/-- Both natural actions apply the same determinant-one matrix to each vector. -/
theorem pointCommutator_eq_binaryNatural : PointCommutator.representation =
    SL2OrthogonalCover.binaryNatural (F := F) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  funext i
  rfl

end Representation.SL2FourNatural

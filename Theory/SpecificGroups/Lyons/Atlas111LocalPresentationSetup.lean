module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIdentificationSetup
public import Theory.SpecificGroups.G2Five.AtlasPresentation

/-!
# The matrix relations for the proposed local identification

Assign the two generators of the 22-relator presentation to the exact outputs
of the ATLAS subgroup program. The relation predicate is separate from the
identification theorem so arithmetic certificates can be imported by the latter
without a dependency cycle. It asserts only concrete matrix identities.

Sources and literal data: `Atlas111OrderSource/` and
`G2Five/AtlasPresentationSource/`.
-/

namespace Lyons.OrderCertificate

/-- The presentation generators are assigned to the exact ATLAS outputs. -/
@[expose] public def localMatrixAssignment (b : Bool) : AtlasMatrixˣ :=
  if b then (max1Program atlasA atlasB).2 else (max1Program atlasA atlasB).1

/-- Relations to be certified by matrix arithmetic, without a recognition assumption. -/
@[expose] public def LocalPresentationRelations : Prop :=
  ∀ i, FreeGroup.lift localMatrixAssignment (G2Five.AtlasPresentation.relator i) = 1

end Lyons.OrderCertificate

module

public import Theory.SpecificGroups.G2Five.AtlasPresentation
public import Theory.SpecificGroups.G2Five.AtlasOctonionPair
public import Theory.SpecificGroups.G2Five.AtlasOctonionRelationProducts

/-!
# The fixed octonion pair satisfies the G₂(5) presentation

The 22 matrix word certificates are transferred to the actual octonion
automorphisms by the injectivity of their coordinate representation. This
proves the relations without any presentation recognition or order assumption.

Sources: `AtlasPresentation.lean` for the literal relators and their ATLAS/GAP
provenance; `AtlasOctonionPair.lean` for the explicit root/Weyl pair. The checked
products and their generator are documented in
`AtlasOctonionSource/RelationCertificates.md`.
-/

namespace G2Five.AtlasPresentation

/-- Every fixed relator holds on the genuine split-octonion generator pair. -/
public theorem octonionGenerator_relators (i : Fin 22) :
    FreeGroup.lift octonionGenerator (relator i) = 1 := by
  apply octonionMatrix_injective
  rw [map_one, RelationCertificate.eval_relator, RelationCertificate.relators_matrix]

end G2Five.AtlasPresentation

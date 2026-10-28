module
public import Theory.SpecificGroups.G2.MultiplierOrdinary.PositiveRelations.Collection
/-!
# Pairwise relations in the concrete G₂ model

The ten commuting pairs and five polynomial interchange formulas are checked
against the actual six-coordinate product law. This fixes their signs and
coefficients independently of the central-extension argument. The identity
projection here is used only to verify the base formulas; it is not substituted
for an arbitrary cover or for the canonical universal projection.

Source: the attributed ATLAS `Unipotent` product law; the central-cover
application is Aschbacher–Smith I.1.3–I.1.4 and GLS III §6.1.
-/

@[expose] public section
namespace Atlas.G2.MultiplierOrdinary
variable {F : Type*} [Field F]

def modelRootSections : RootSections (MonoidHom.id (Model F)) where
  root := positiveRootHom
  project := fun _ => rfl

theorem model_collectionRelations : (modelRootSections (F := F)).CollectionRelations := by
  constructor
  · constructor
    · intro s t
      simpa [modelRootSections, RootSections.x, positiveRootHom, positiveRoot,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,s,0,0,0,0] ![t,0,0,0,0,0])
    · intro s t
      simpa [modelRootSections, RootSections.x, positiveRootHom, positiveRoot,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,s,0,0,0] ![t,0,0,0,0,0])
    · intro s t
      simpa [modelRootSections, RootSections.x, positiveRootHom, positiveRoot,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,s,0,0,0] ![0,t,0,0,0,0])
    · intro s t
      simpa [modelRootSections, RootSections.x, positiveRootHom, positiveRoot,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,s,0,0] ![t,0,0,0,0,0])
    · intro s t
      simpa [modelRootSections, RootSections.x, positiveRootHom, positiveRoot,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,s,0,0] ![0,t,0,0,0,0])
    · intro s t
      simpa [modelRootSections, RootSections.x, positiveRootHom, positiveRoot,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,s,0] ![t,0,0,0,0,0])
    · intro s t
      simpa [modelRootSections, RootSections.x, positiveRootHom, positiveRoot,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,s,0] ![0,0,t,0,0,0])
    · intro s t
      simpa [modelRootSections, RootSections.x, positiveRootHom, positiveRoot,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,s,0] ![0,0,0,t,0,0])
    · intro s t
      simpa [modelRootSections, RootSections.x, positiveRootHom, positiveRoot,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,0,s] ![t,0,0,0,0,0])
    · intro s t
      simpa [modelRootSections, RootSections.x, positiveRootHom, positiveRoot,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,0,s] ![0,t,0,0,0,0])
  · constructor
    · intro s t
      simpa [modelRootSections, RootSections.x, positiveRootHom, positiveRoot,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,s,0,0] ![0,0,t,0,0,0])
    · intro s t
      simpa [modelRootSections, RootSections.x, positiveRootHom, positiveRoot,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,s,0] ![0,t,0,0,0,0])
    · intro s t
      simpa [modelRootSections, RootSections.x, positiveRootHom, positiveRoot,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,0,s] ![0,0,t,0,0,0])
    · intro s t
      simpa [modelRootSections, RootSections.x, positiveRootHom, positiveRoot,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,0,s] ![0,0,0,t,0,0])
    · intro s t
      simpa [modelRootSections, RootSections.x, positiveRootHom, positiveRoot,
        unipotentProduct, unipotentProductParameters] using
        (unipotentProduct_mul ![0,0,0,0,0,s] ![0,0,0,0,t,0])
end Atlas.G2.MultiplierOrdinary
end

module

public import Theory.SpecificGroups.G2Five.AtlasPresentation
public import Theory.SpecificGroups.G2Five.AtlasOctonionPair
public import Theory.SpecificGroups.G2Five.AtlasOctonionRelations
public import Theory.SpecificGroups.G2Five.AtlasOctonionGeneration

/-!
# The octonion quotient of the fixed G₂(5) presentation

The explicit pair consists of actual split-octonion automorphisms. Its certified
22 relations define a homomorphism from the fixed presentation, and its proved
generation makes that homomorphism surjective. The conditional interface is
retained, and `octonionHom` assembles both certificates without hypotheses.

Sources: `AtlasPresentation.lean` for the literal presentation and its universal
property, `AtlasOctonionPair.lean` for the chosen root/Weyl expressions, and
`AtlasOctonionRelations.lean` and `AtlasOctonionGeneration.lean` for the checked
relation and generation certificates.
-/

namespace G2Five.AtlasPresentation

/-- The fixed pair descends as soon as its literal relations are certified. -/
@[expose] public def octonionHomOfRelators
    (hrel : ∀ i, FreeGroup.lift octonionGenerator (relator i) = 1) :
    Model →* Atlas.G2.Model (ZMod 5) := hom octonionGenerator hrel

@[simp] public theorem octonionHomOfRelators_generator
    (hrel : ∀ i, FreeGroup.lift octonionGenerator (relator i) = 1) (b : Bool) :
    octonionHomOfRelators hrel (generator b) = octonionGenerator b :=
  hom_generator octonionGenerator hrel b

/-- Generation of the concrete pair proves surjectivity of the descended map. -/
public theorem octonionHomOfRelators_surjective
    (hrel : ∀ i, FreeGroup.lift octonionGenerator (relator i) = 1)
    (hgen : Subgroup.closure
      ({octonionGenerator false, octonionGenerator true} :
        Set (Atlas.G2.Model (ZMod 5))) = ⊤) :
    Function.Surjective (octonionHomOfRelators hrel) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases hx with rfl | hx
  · exact ⟨generator false, octonionHomOfRelators_generator hrel false⟩
  · obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨generator true, octonionHomOfRelators_generator hrel true⟩

/-- The certified quotient map onto the split-octonion automorphism group. -/
@[expose] public def octonionHom : Model →* Atlas.G2.Model (ZMod 5) :=
  octonionHomOfRelators octonionGenerator_relators

@[simp] public theorem octonionHom_generator (b : Bool) :
    octonionHom (generator b) = octonionGenerator b :=
  octonionHomOfRelators_generator octonionGenerator_relators b

/-- The two images generate the full split-octonion automorphism group. -/
public theorem octonionHom_surjective : Function.Surjective octonionHom :=
  octonionHomOfRelators_surjective octonionGenerator_relators closure_octonionGenerator

end G2Five.AtlasPresentation

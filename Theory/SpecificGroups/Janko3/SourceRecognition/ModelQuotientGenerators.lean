module
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.ModelRelations

/-!
# Actual ATLAS generators in a quotient of the concrete model

A proved surjection from the concrete model transports its two generators
and all eight certified relators. No identification of the quotient with the
model, or finiteness of the abstract presentation, is needed.
-/

public section
namespace Sporadic.Janko3.SourceRecognition
open Subgroup RecognitionPresentation

/-- Every actual quotient of the concrete model inherits its specified
ATLAS generating pair and all eight relators. -/
theorem hasGenerators_of_model_surjection
    {G : Type*} [Group G] (f : Model →* G) (hf : Function.Surjective f) :
    HasGenerators G := by
  refine ⟨f a,f b,?_,?_⟩
  · have hm := congrArg (Subgroup.map f) generators_closure
    rw [MonoidHom.map_closure,map_top_of_surjective f hf] at hm
    simpa only [Set.image_insert_eq,Set.image_singleton] using hm
  · intro i
    rw [←map_relator f a b i,model_satisfies i,map_one]

end Sporadic.Janko3.SourceRecognition

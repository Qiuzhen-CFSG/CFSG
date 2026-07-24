/-
Authors: OpenAI
-/

module

public import Submission.FeitThompson.Representation.ConjugateRep
public import Submission.FeitThompson.Representation.SubrepresentationLattice
public import Submission.FeitThompson.Representation.RepEquiv

/-!
# Isaacs Lemma 6.4

A source-faithful statement of Isaacs, *Character Theory of Finite Groups*,
Lemma 6.4. The source's conjugate submodule `Wg` is written as the image of
`W` under the ambient representation operator corresponding to `g^-1`, and
conjugacy of modules is written directly with `Representation.conjugateRep`.
-/

noncomputable section

namespace BenderSuzuki
namespace External
namespace Isaacs
namespace VI

/-- Isaacs, Character Theory of Finite Groups, Lemma 6.4. -/
public theorem isaacs_lemma_6_4
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (H : Subgroup G) [H.Normal]
    (W : Subrepresentation (rho.comp H.subtype)) :
    (forall g : G,
      exists Wg : Subrepresentation (rho.comp H.subtype),
        Wg.toSubmodule = Submodule.map (rho g⁻¹) W.toSubmodule ∧
          Nonempty (Wg.toRepresentation ≃ₗ
            Representation.conjugateRep (G := G) (H := H) W.toRepresentation g)) ∧
      (forall {M : Type*} [AddCommGroup M] [Module F M]
        (sigma : Representation F H M),
        (exists g : G, Nonempty (sigma ≃ₗ
          Representation.conjugateRep (G := G) (H := H) W.toRepresentation g)) ->
          exists g : G, exists Wg : Subrepresentation (rho.comp H.subtype),
            Wg.toSubmodule = Submodule.map (rho g⁻¹) W.toSubmodule ∧
              Nonempty (sigma ≃ₗ Wg.toRepresentation)) ∧
      (forall U : Subrepresentation (rho.comp H.subtype),
        Nonempty (U.toRepresentation ≃ₗ W.toRepresentation) ->
          forall g : G,
            exists Ug Wg : Subrepresentation (rho.comp H.subtype),
              Ug.toSubmodule = Submodule.map (rho g⁻¹) U.toSubmodule ∧
                Wg.toSubmodule = Submodule.map (rho g⁻¹) W.toSubmodule ∧
                  Nonempty (Ug.toRepresentation ≃ₗ Wg.toRepresentation)) := by
  constructor
  · intro g
    refine ⟨Representation.conjugateSubrepresentation rho H W g, ?_, ?_⟩
    · exact Representation.conjugateSubrepresentation_toSubmodule rho H W g
    exact ⟨Representation.conjugateSubrepresentationEquiv rho H W g⟩
  constructor
  · intro M _ _ sigma hsigma
    rcases hsigma with ⟨g, ⟨e⟩⟩
    refine ⟨g, Representation.conjugateSubrepresentation rho H W g, ?_, ?_⟩
    · exact Representation.conjugateSubrepresentation_toSubmodule rho H W g
    exact ⟨e.trans (Representation.conjugateSubrepresentationEquiv rho H W g).symm⟩
  · intro U hUW g
    rcases hUW with ⟨eUW⟩
    let Ug := Representation.conjugateSubrepresentation rho H U g
    let Wg := Representation.conjugateSubrepresentation rho H W g
    refine ⟨Ug, Wg, ?_, ?_, ?_⟩
    · exact Representation.conjugateSubrepresentation_toSubmodule rho H U g
    · exact Representation.conjugateSubrepresentation_toSubmodule rho H W g
    let eUg := Representation.conjugateSubrepresentationEquiv rho H U g
    let eWg := Representation.conjugateSubrepresentationEquiv rho H W g
    let eConj := Representation.conjugateRepEquiv eUW g
    exact ⟨eUg.trans (eConj.trans eWg.symm)⟩

end VI
end Isaacs
end External
end BenderSuzuki

module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Contracts
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Permutation

/-!
# Descent through the marked HS presentation

The sourced universal group has a proved surjection onto the literal
permutation carrier. If that map is injective and the two literal matrices
satisfy its thirteen relations, invert the canonical isomorphism and apply
the universal property to the matrix pair. This constructs a representation
and proves both required generator images, without any irreducibility input.

Both finite-matrix relations and abstract presentation faithfulness remain
explicit obligations. This module does not assert `matrixDescentExists`.
Source: ATLAS HSG1-P1.M, HSd2G1-f2r1408B0 and HSd2G1-max1W1; see
`Descent/source/README.md` and `source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408

open Sporadic.LeechRelated.HS

/-- The two independent certificates construct exactly the requested
marked action on the permutation-defined carrier. -/
theorem matrixDescentExists_of_presentation
    (hfaithful : IsSimpleGroup Carrier → Function.Injective AtlasPresentation.toCarrier)
    (hmatrices : MatrixRelations) : MatrixDescentExists := by
  intro hs
  obtain ⟨a, b, ha, hb, hrel⟩ := hmatrices
  let e : AtlasPresentation.Universal ≃* Carrier :=
    MulEquiv.ofBijective AtlasPresentation.toCarrier
      ⟨hfaithful hs, AtlasPresentation.toCarrier_surjective⟩
  let f : Carrier →* Matˣ :=
    (AtlasPresentation.pairHom a b hrel).comp e.symm.toMonoidHom
  let ρ : Representation (ZMod 2) Carrier Vector :=
    Matrix.toLinAlgEquiv'.toAlgHom.toMonoidHom.comp ((Units.coeHom Mat).comp f)
  have hea : e.symm generatorAElement = AtlasPresentation.generator false := by
    apply e.injective
    exact (e.apply_symm_apply _).trans AtlasPresentation.toCarrier_generator_false.symm
  have heb : e.symm generatorBElement = AtlasPresentation.generator true := by
    apply e.injective
    exact (e.apply_symm_apply _).trans AtlasPresentation.toCarrier_generator_true.symm
  refine ⟨ρ, ?_, ?_⟩
  · change LinearMap.toMatrix'
      (Matrix.toLin' (AtlasPresentation.pairHom a b hrel (e.symm generatorAElement) : Mat)) = _
    rw [hea, AtlasPresentation.pairHom_generator_false, LinearMap.toMatrix'_toLin', ha]
  · change LinearMap.toMatrix'
      (Matrix.toLin' (AtlasPresentation.pairHom a b hrel (e.symm generatorBElement) : Mat)) = _
    rw [heb, AtlasPresentation.pairHom_generator_true, LinearMap.toMatrix'_toLin', hb]

end Representation.HigmanSims.LargeModels.Restricted1408

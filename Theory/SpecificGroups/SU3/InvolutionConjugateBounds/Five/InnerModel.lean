module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.InnerModel.Maximality
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.InnerModel.Generators
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.InnerModel.Embedding

/-!
# The maximal inner A₇ model in PSU₃(5)

The explicit special-unitary matrices give an actual projective embedding
of A₇ into the standard PSU₃(5), retaining the scalar kernel. Under inherited
simplicity, the maximality theorem makes its image a maximal proper subgroup.
The alternating-group generation theorem supplies three elements of order
two whose subgroup closure is all of A₇. Together these discharge the entire
`InnerModel` input to `Five.fourBoundAtFive_of_models`.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11, used in Aschbacher–Smith K.2, printed p.453.
-/

public section

namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five

/-- The actual embedding suffices for the full inner-model contract;
maximality and the involutory generating triple are proved here. -/
theorem innerModel_of_embedding
    (hembed : ∀ [IsSimpleGroup StandardGroup],
      ∃ f : alternatingGroup (Fin 7) →* StandardGroup, Function.Injective f) :
    InnerModel := by
  intro _
  obtain ⟨f, hf⟩ := hembed
  exact ⟨f, hf, alternatingSeven_range_isCoatom f hf,
    alternatingSeven_involution_generators⟩

/-- The standard PSU₃(5) contains a maximal A₇ with three involutory generators,
under precisely the inherited simplicity hypothesis in `InnerModel`. -/
theorem innerModel : InnerModel :=
  innerModel_of_embedding (by
    intro _
    exact exists_alternatingSeven_embedding)

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five

module

public import Theory.SpecificGroups.ExoticTwoGroup.LocalStructureTransport
public import Theory.SpecificGroups.ExoticTwoGroup.LocalCentralizerPowers
public import Theory.SpecificGroups.ExoticTwoGroup.LocalModelPresentation
public import Theory.SpecificGroups.ExoticTwoGroup.LocalModelStructure

/-!
# Assembly of the exotic presentation computations

The explicit iterated semidirect product in `LocalModel` satisfies the
six-generator presentation and has 256 elements. `LocalCentralizerPowers`
constructs the characteristic lines in its two involution centralizers.
`LocalModelStructure` completes the finite involution and centralizer census,
and `LocalModelPresentation` identifies every presentation with the model,
preserving all six generators. Transporting the model calculation along this
identification gives the unconditional local-structure constructor below.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.4(c), p.386 and p.396.
-/

namespace ExoticTwoGroup.Presentation

/-- The concrete census and a marked identification imply all local fields. -/
public theorem localStructure_of_model
    {P : Type*} [Group P] (d : ExoticTwoGroup.Presentation P)
    (hmodel : LocalModel.presentation.LocalStructure)
    (he : ∃ e : LocalModel.Model ≃* P,
      e LocalModel.a = d.a ∧ e LocalModel.b = d.b ∧
      e LocalModel.g₁ = d.g₁ ∧ e LocalModel.g₂ = d.g₂ ∧
      e LocalModel.t = d.t ∧ e LocalModel.z₀ = d.z₀) : d.LocalStructure := by
  obtain ⟨e, ha, hb, hg₁, hg₂, ht, hz₀⟩ := he
  exact LocalStructure.of_equiv LocalModel.presentation d e ha hb hg₁ hg₂ ht hz₀ hmodel

/-- Every finite exotic presentation has the involution classes, centralizers,
and characteristic centralizer lines calculated by Janko–Thompson. -/
public theorem localStructure
    {P : Type*} [Group P] [Finite P] (d : ExoticTwoGroup.Presentation P) :
    d.LocalStructure :=
  d.localStructure_of_model LocalModel.localStructure (LocalModel.exists_marked_equiv d)

end ExoticTwoGroup.Presentation

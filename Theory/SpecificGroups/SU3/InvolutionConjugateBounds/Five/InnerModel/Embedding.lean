module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.InnerModel.Embedding.Relations
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.Inputs
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.FormTransport

/-!
# An actual projective A₇ subgroup of PSU₃(5)

Five explicit special-unitary matrices over a quadratic field of order 25
satisfy Suzuki's alternating-group presentation modulo scalars. Their
projective images give a nontrivial homomorphism from A₇, which is injective
by simplicity of A₇. An orthonormal basis and the finite-field isomorphism
transport it into the literal identity-Gram projective matrix image used by
`StandardGroup`. No simplicity assumption on PSU₃(5) is needed.

This supplies the embedding used by `innerModel_of_embedding`.
Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11, used in Aschbacher–Smith K.2, printed p.453.
The concrete generator matrices come from the repository's checked exceptional
A₇ certificates in `Theory.Alternating.theorem_5_2_3`.
-/

public section
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A₇ embeds in the actual projective special unitary matrix group PSU₃(5). -/
theorem exists_alternatingSeven_embedding :
    ∃ f : alternatingGroup (Fin 7) →* StandardGroup, Function.Injective f := by
  obtain ⟨f, hf⟩ := Embedding.exists_embedding_matrixForm
  obtain ⟨e⟩ := Matrix.SU3.InnerThreeRank.exists_projective_equiv_standard
    5 Embedding.F25 Embedding.matrixForm Embedding.F25.card
    Embedding.F25.conjugation_eq_fifth
  exact ⟨e.toMonoidHom.comp f, e.injective.comp hf⟩

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five

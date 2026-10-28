module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary.BlockModel
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary.Splitting
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary.BlockGeometry.MatrixEmbedding

/-!
# Transport and splitting of the marked unitary block-pair geometry

The coordinate calculation proves both reflection fusions. An actual
orthonormal basis transports the resulting marked block model into the
original stored Hermitian form. The existing double-cover argument then
gives a section over the literal inclusion range, with the original
projection triangle unchanged.

The semidirect-product matrix embedding remains an explicit input here.
Consequently these are conditional assembly results, not an assertion of
the existence of the block model or the unitary multiplier theorem.
The final unconditional construction belongs in this module once the
coordinate embedding has been constructed.

Source: Aschbacher--Smith I.1.4(3), printed p.408, and GLS3 §6.1.
-/

public section
open BenderSuzuki.MatrixGroups
open HermitianForm.IdentityGram

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary

variable {F : Type*} [Field F] {J K : HermitianForm 4 F} {q : ℕ} [Fact q.Prime]

/-- Transport all marked maps and both conjugacies along one group equivalence. -/
def BlockModel.map (m : BlockModel J q) (e : J.specialSubgroup ≃* K.specialSubgroup) :
    BlockModel K q where
  action := m.action
  inclusion := e.toMonoidHom.comp m.inclusion
  injective := e.injective.comp m.injective
  transverse := e.toMonoidHom.comp m.transverse
  transverse_injective := e.injective.comp m.transverse_injective
  torus := m.torus
  torus_pow := m.torus_pow
  rotation_eq := congrArg e m.rotation_eq
  reflection_zero_conjugate := e.toMonoidHom.map_isConj m.reflection_zero_conjugate
  reflection_one_conjugate := e.toMonoidHom.map_isConj m.reflection_one_conjugate

/-- Identity-coordinate matrix data gives the marked block model for the
original form, by genuine conjugation through an orthonormal basis. -/
theorem nonempty_blockModel_of_matrixEmbedding [Finite F]
    (J : HermitianForm 4 F) (hq : 3 < q)
    (hc : Nat.card F = q ^ 2) (hj : ∀ x, J.conj x = x ^ q)
    (m : BlockGeometry.MatrixEmbedding (identityGram J) q) : Nonempty (BlockModel J q) := by
  obtain ⟨C, e, ep, hC, _, _⟩ := exists_identityGram_transport J q Fact.out hc hj
  let b := m.toBlockModel rfl hq hc hj
  exact ⟨b.map (specialEquiv J C hC).symm⟩

/-- Application to an actual degree-two central extension, retaining exactly
`f.comp s = range.subtype`. The matrix embedding is the only extra geometric
input; neither fusion nor a lifting hypothesis is required. -/
theorem exists_section_of_matrixEmbedding [Finite F]
    (J : HermitianForm 4 F) (hq : 3 < q)
    (hc : Nat.card F = q ^ 2) (hj : ∀ x, J.conj x = x ^ q)
    (m : BlockGeometry.MatrixEmbedding (identityGram J) q)
    {E : Type*} [Group E] [Finite E]
    (f : E →* J.specialSubgroup) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center E) (hcard : Nat.card f.ker = 2) :
    ∃ b : BlockModel J q, ∃ s : b.inclusion.range →* E,
      f.comp s = b.inclusion.range.subtype := by
  obtain ⟨b⟩ := nonempty_blockModel_of_matrixEmbedding J hq hc hj m
  obtain ⟨s, hs⟩ := exists_section_on_block_model J hq b f hf hcentral hcard
  exact ⟨b, s, hs⟩

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary

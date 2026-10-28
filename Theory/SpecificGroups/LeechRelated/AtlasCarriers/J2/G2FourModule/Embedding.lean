module

public import Theory.Representation.G2NaturalFaithfulness
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.Extension
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.BinaryIrreducibility

/-!
# The marked Hall--Janko embedding and its irreducible binary module

The natural binary action is faithful for every marked embedding, by the
structural faithfulness theorem for the octonion quotient. To construct a
marking from an inner embedding, Frobenius compatibility need only be checked
on the two published generators: the permutation involution fixes the first
and inverts the second. The extension construction then supplies the outer
homomorphism, its injectivity, and both required marking identities.

The certified presentation comparison and octonion pair now construct this
inner embedding. Applying the independent irreducibility theorem gives a
faithful irreducible binary module on the actual natural quotient, with the
specified field involution on the literal permutation extension. Only the
inherited simplicity of the actual degree-100 carrier remains a hypothesis.

This supplies the marked model used in Aschbacher--Smith, K.4.5,
printed p.460/PDF p.471. Recognition of the arbitrary source module and the
offender calculations remain with their source consumers. The imported
permutation, presentation and octonion certificates retain their ATLAS
attribution and license.
-/

@[expose] public noncomputable section

namespace Sporadic.LeechRelated.J2.G2FourModule
open ExceptionalParabolics Atlas.G2.Natural.BinarySemilinear

namespace MarkedEmbedding
/-- The binary natural action is faithful for every actual marking. -/
theorem innerRepresentation_injective (d : MarkedEmbedding) :
    Function.Injective d.innerRepresentation :=
  (Atlas.G2.Natural.binary_action_injective F).comp d.inner_injective
end MarkedEmbedding

namespace Embedding
/-- The two published generators suffice to check the field marking. -/
theorem equivariant_of_generator_values (f : Carrier →* M)
    (ha : f GeneratorPair.a = Atlas.G2.fieldEquiv fourFrobenius (f GeneratorPair.a))
    (hb : (f GeneratorPair.b)⁻¹ = Atlas.G2.fieldEquiv fourFrobenius (f GeneratorPair.b)) :
    ∀ j, f (involutionAut j) = Atlas.G2.fieldEquiv fourFrobenius (f j) := by
  have heq : f.comp involutionAut.toMonoidHom =
      (Atlas.G2.fieldEquiv fourFrobenius).toMonoidHom.comp f := by
    apply MonoidHom.eq_of_eqOn_dense GeneratorPair.closure_pair_eq_top
    intro j hj
    rcases Set.mem_insert_iff.mp hj with rfl | hj
    · simpa using ha
    · rw [Set.mem_singleton_iff] at hj
      subst j
      simpa using hb
  exact fun j => DFunLike.congr_fun heq j

/-- An injective inner homomorphism with the two field equations supplies all
of the marked outer-extension data. Its existence remains a separate result. -/
def markedOfGeneratorValues (f : Carrier →* M) (hf : Function.Injective f)
    (ha : f GeneratorPair.a = Atlas.G2.fieldEquiv fourFrobenius (f GeneratorPair.a))
    (hb : (f GeneratorPair.b)⁻¹ = Atlas.G2.fieldEquiv fourFrobenius (f GeneratorPair.b)) :
    MarkedEmbedding :=
  markedOfEquivariant f hf (equivariant_of_generator_values f ha hb)

variable [IsSimpleGroup Carrier]

/-- The actual degree-100 Hall--Janko carrier and its literal permutation
extension embedded in G₂(4) and its inner-field extension. -/
def markedEmbedding : MarkedEmbedding := InnerRealization.markedEmbedding

/-- The inner map is the certified presentation-to-octonion realization. -/
@[simp] theorem markedEmbedding_inner :
    markedEmbedding.inner = InnerRealization.inner := rfl

/-- Agreement with the literal inclusion of J₂ in its permutation extension. -/
@[simp] theorem markedEmbedding_on_inner (j : Carrier) :
    markedEmbedding.outer (intoExtension j) =
      SemidirectProduct.inl (InnerRealization.inner j) :=
  InnerRealization.markedEmbedding_on_inner j

/-- The specified outside involution maps to the specified coefficient Frobenius. -/
@[simp] theorem markedEmbedding_on_involution :
    markedEmbedding.outer extensionInvolution = SemidirectProduct.inr fourFrobenius :=
  InnerRealization.markedEmbedding_on_involution

/-- Faithfulness of the literal binary action of the constructed marking. -/
theorem markedEmbedding_innerRepresentation_injective :
    Function.Injective markedEmbedding.innerRepresentation :=
  markedEmbedding.innerRepresentation_injective

/-- Binary irreducibility for the constructed model, independent of source
module recognition. -/
theorem markedEmbedding_innerRepresentation_irreducible :
    Representation.IsIrreducible markedEmbedding.innerRepresentation :=
  markedEmbedding.innerRepresentation_irreducible

/-- The complete marked-model input for source recognition: the marking and
both representation properties are constructed, rather than assumed. -/
theorem exists_markedEmbedding : ∃ d : MarkedEmbedding,
    Function.Injective d.innerRepresentation ∧
      Representation.IsIrreducible d.innerRepresentation :=
  ⟨markedEmbedding, markedEmbedding_innerRepresentation_injective,
    markedEmbedding_innerRepresentation_irreducible⟩
end Embedding
end Sporadic.LeechRelated.J2.G2FourModule

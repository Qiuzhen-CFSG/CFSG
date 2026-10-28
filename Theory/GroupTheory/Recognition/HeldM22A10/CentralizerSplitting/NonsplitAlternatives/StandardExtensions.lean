module

public import Theory.GroupTheory.Recognition.HeldM22A10.Setup
public import Theory.GroupTheory.Recognition.HeldM22A10.LocalStructure
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.Actions
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.QuotientAction
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitModels
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.FactorSets
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.Parity
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.Nonsplitting
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.Realizations
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.PermutationCohomology
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.TwistedCohomology

/-!
# From binary factor sets to the Held centralizer alternatives

A supplied equivalence of the actual quotient action with a binary action
transports the specified elementary kernel into those coordinates. A normalized
section then identifies the centralizer with the corresponding factor-set
extension, preserving the actual projection and hence its specified kernel.
The trivial class yields a complement; a factor set equivalent to the parity
representative produces a multiplicative equivalence to any realization of it.

The imported `Realizations` module identifies the two parity representatives
with the exact published permutation models. `Nonsplitting` proves that both
are nontrivial and have no complement to their specified kernels. Thus the
ordinary and twisted extension steps in Huppert--Blackburn, *Finite Groups III*,
XII.1.18(b), p.314, follow from the complete factor-set classifications proved
in `PermutationCohomology` and `TwistedCohomology`. The final two theorems give
the complement or model alternative assuming only the supplied equivalence of
the quotient action. Action normalization and ambient exclusion of the nonsplit
models belong to the separate assembly of the source splitting theorem.
-/

@[expose] public section

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions
open LocalModelDichotomy AbelianExtension
universe u v
variable {G : Type u} [Group G] (D : LocalData G)

/-- Coordinates change only the kernel inclusion, retaining the actual quotient. -/
noncomputable def binaryExtension (e : D.kernel ≃* BinaryFour) :
    GroupExtension BinaryFour D.centralizer SymmetricFour where
  inl := D.kernel.subtype.comp e.symm.toMonoidHom
  rightHom := D.extensionQuotient
  inl_injective := Subtype.val_injective.comp e.symm.injective
  range_inl_eq_ker_rightHom := by
    rw [D.extensionQuotient_ker]
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (e.symm v).property
    · intro hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      change (e.symm (e ⟨x, hx⟩) : D.centralizer) = x
      rw [e.symm_apply_apply]
  rightHom_surjective := D.extensionQuotient_surjective

/-- Equivariant kernel coordinates express the original conjugation formula. -/
theorem binaryExtension_conjugation (e : D.kernel ≃* BinaryFour)
    (α : SymmetricFour →* MulAut BinaryFour)
    (he : ∀ s f, e (D.quotientKernelAction s f) = α s (e f))
    (g : D.centralizer) (n : BinaryFour) :
    (binaryExtension D e).inl (α ((binaryExtension D e).rightHom g) n) =
      g * (binaryExtension D e).inl n * g⁻¹ := by
  change (e.symm (α (D.extensionQuotient g) n) : D.centralizer) =
    g * (e.symm n : D.centralizer) * g⁻¹
  rw [← D.extensionConjugation_apply]
  apply congrArg Subtype.val
  apply e.injective
  rw [e.apply_symm_apply, ← D.quotientKernelAction_quotient, he, e.apply_symm_apply]

/-- Every supplied action equivalence gives actual factor-set coordinates on H. -/
theorem exists_factorSet_realization [Finite G]
    (α : SymmetricFour →* MulAut BinaryFour)
    (hα : ActionEquivalent D.quotientBinaryAction α) :
    ∃ c : FactorSet α, ∃ e : c.Extension ≃* D.centralizer,
      ∀ x, D.extensionQuotient (e x) = c.projection x := by
  obtain ⟨a, ha⟩ := hα
  let e := D.kernelBinaryEquiv.trans a
  have he : ∀ s f, e (D.quotientKernelAction s f) = α s (e f) := by
    intro s f
    change a (D.kernelBinaryEquiv (D.quotientKernelAction s f)) =
      α s (a (D.kernelBinaryEquiv f))
    rw [← D.quotientBinaryAction_apply]
    exact ha s (D.kernelBinaryEquiv f)
  let S := binaryExtension D e
  have hact := binaryExtension_conjugation D e α he
  let σ := normalizedSection S
  have hσ : σ 1 = 1 := normalizedSection_one S
  let c := sectionFactorSet S α hact σ hσ
  refine ⟨c, sectionEquiv S α hact σ hσ, ?_⟩
  exact sectionEquiv_projection S α hact σ hσ

/-- Transfer the trivial class to a complement of the specified local kernel. -/
theorem complement_of_factorSet_trivial
    {α : SymmetricFour →* MulAut BinaryFour} (c : FactorSet α)
    (e : c.Extension ≃* D.centralizer)
    (he : ∀ x, D.extensionQuotient (e x) = c.projection x)
    (hc : c.Equivalent (FactorSet.trivial α)) :
    ∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K := by
  obtain ⟨s, hs⟩ := c.exists_section_of_equivalent_trivial hc
  let t := e.toMonoidHom.comp s
  have ht : ∀ q, D.extensionQuotient (t q) = q := fun q => (he (s q)).trans (hs q)
  refine ⟨t.range, ?_⟩
  rw [← D.extensionQuotient_ker]
  exact isComplement_ker_range_of_section D.extensionQuotient t ht

/-- Classification of factor sets and realization of one specified class
suffice for the desired alternative. Both inputs remain explicit here. -/
theorem alternatives_of_factorSet_classification [Finite G]
    {M : Type v} [Group M]
    (α : SymmetricFour →* MulAut BinaryFour)
    (hα : ActionEquivalent D.quotientBinaryAction α)
    (d : FactorSet α)
    (hclasses : ∀ c : FactorSet α,
      c.Equivalent (FactorSet.trivial α) ∨ c.Equivalent d)
    (hmodel : Nonempty (d.Extension ≃* M)) :
    (∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K) ∨
      Nonempty (D.centralizer ≃* M) := by
  obtain ⟨c, e, he⟩ := exists_factorSet_realization D α hα
  obtain ⟨f⟩ := hmodel
  rcases hclasses c with hc | hc
  · exact Or.inl (complement_of_factorSet_trivial D c e he hc)
  · obtain ⟨b, hb, h⟩ := hc
    exact Or.inr ⟨(e.symm.trans (c.equivalenceOfCorrection d b hb h)).trans f⟩

/-- Assemble the ordinary-action branch once its two independent inputs hold. -/
theorem permutation_alternative_of_classification [Finite G]
    (hα : ActionEquivalent D.quotientBinaryAction permutationAction)
    (hclasses : ∀ c : FactorSet permutationAction,
      c.Equivalent (FactorSet.trivial permutationAction) ∨ c.Equivalent permutationFactorSet)
    (hmodel : Nonempty (permutationFactorSet.Extension ≃* NonsplitModels.First)) :
    (∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K) ∨
      Nonempty (D.centralizer ≃* NonsplitModels.First) :=
  alternatives_of_factorSet_classification D permutationAction hα
    permutationFactorSet hclasses hmodel

/-- Assemble the twisted-action branch once its two independent inputs hold. -/
theorem twisted_alternative_of_classification [Finite G]
    (hα : ActionEquivalent D.quotientBinaryAction twistedAction)
    (hclasses : ∀ c : FactorSet twistedAction,
      c.Equivalent (FactorSet.trivial twistedAction) ∨ c.Equivalent twistedFactorSet)
    (hmodel : Nonempty (twistedFactorSet.Extension ≃* NonsplitModels.Second)) :
    (∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K) ∨
      Nonempty (D.centralizer ≃* NonsplitModels.Second) :=
  alternatives_of_factorSet_classification D twistedAction hα
    twistedFactorSet hclasses hmodel

/-- The ordinary-action alternative, using the proved first-model comparison.
Only completeness of the two factor-set classes remains as an extra premise. -/
theorem permutation_alternative_of_factorSet_classes [Finite G]
    (hα : ActionEquivalent D.quotientBinaryAction permutationAction)
    (hclasses : ∀ c : FactorSet permutationAction,
      c.Equivalent (FactorSet.trivial permutationAction) ∨ c.Equivalent permutationFactorSet) :
    (∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K) ∨
      Nonempty (D.centralizer ≃* NonsplitModels.First) :=
  permutation_alternative_of_classification D hα hclasses ⟨permutationFactorSetEquivFirst⟩

/-- The twisted-action alternative, using the proved second-model comparison.
Only completeness of the two factor-set classes remains as an extra premise. -/
theorem twisted_alternative_of_factorSet_classes [Finite G]
    (hα : ActionEquivalent D.quotientBinaryAction twistedAction)
    (hclasses : ∀ c : FactorSet twistedAction,
      c.Equivalent (FactorSet.trivial twistedAction) ∨ c.Equivalent twistedFactorSet) :
    (∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K) ∨
      Nonempty (D.centralizer ≃* NonsplitModels.Second) :=
  twisted_alternative_of_classification D hα hclasses ⟨twistedFactorSetEquivSecond⟩

/-- For the ordinary quotient action, the specified kernel has a complement
or the centralizer is isomorphic to the first published nonsplit model. -/
theorem permutation_alternative [Finite G]
    (hα : ActionEquivalent D.quotientBinaryAction permutationAction) :
    (∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K) ∨
      Nonempty (D.centralizer ≃* NonsplitModels.First) :=
  permutation_alternative_of_factorSet_classes D hα permutationFactorSet_classes

/-- For the twisted quotient action, the specified kernel has a complement
or the centralizer is isomorphic to the second published nonsplit model. -/
theorem twisted_alternative [Finite G]
    (hα : ActionEquivalent D.quotientBinaryAction twistedAction) :
    (∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K) ∨
      Nonempty (D.centralizer ≃* NonsplitModels.Second) :=
  twisted_alternative_of_factorSet_classes D hα twistedFactorSet_classes

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions

module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.Actions
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.QuotientAction
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ExtraExtensions.Cohomology
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ExtraExtensions.LocalCoordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ExtraExtensions.ThirdRealization
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitModels

/-!
# Classification of the two additional Held extension cases

The twelve-orbit case splits over the specified elementary kernel because
its binary second cohomology vanishes. In the six-orbit case, uniqueness of
the nonzero cohomology class and its genuine nonsplit realization give either
a complement to that same kernel or an actual multiplicative equivalence to
the published third permutation group. The finite cocycle calculations and
the concrete realization are supplied by the imported proofs.

Only the action equivalences remain explicit inputs to the two final helpers.
The proofs do not require ambient simplicity. They supply two branches of
the centralizer alternatives used for Huppert--Blackburn, *Finite Groups III*,
XII.1.18(b), p.314; action normalization and exclusion of the nonsplit models
belong to the separate assembly of that splitting theorem.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)

/-- Vanishing of the twelve-orbit factor sets gives the required complement.
This reduction takes the vanishing calculation as an explicit premise. -/
public theorem twelveOrbit_complement_of_cocycle_vanishing
    (hvanish : ∀ c : FactorSet twelveOrbitAction, c.IsCoboundary)
    (haction : ActionEquivalent D.quotientBinaryAction twelveOrbitAction) :
    ∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K :=
  complement_of_factorSets_coboundaries D hvanish haction

/-- Uniqueness of the nonzero six-orbit class and its concrete realization give
the exact-kernel complement or an actual isomorphism to the third model.
Both the class calculation and the nonsplit realization are explicit premises. -/
public theorem sixOrbit_alternatives_of_cocycle_classification
    (hclasses : ∀ c d : FactorSet sixOrbitAction,
      ¬ c.IsCoboundary → ¬ d.IsCoboundary → c.Cohomologous d)
    (hmodel : ∃ E : ActionExtension sixOrbitAction NonsplitModels.Third,
      ¬ E.factorSet.IsCoboundary)
    (haction : ActionEquivalent D.quotientBinaryAction sixOrbitAction) :
    (∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K) ∨
      Nonempty (D.centralizer ≃* NonsplitModels.Third) := by
  classical
  obtain ⟨e, he⟩ := haction
  let E := localExtension D e he
  by_cases hc : E.factorSet.IsCoboundary
  · obtain ⟨K, hK⟩ := E.complement_of_isCoboundary hc
    exact Or.inl ⟨K, (localExtension_inl_range D e he) ▸ hK⟩
  · obtain ⟨E', hE'⟩ := hmodel
    exact Or.inr ⟨E.equivOfCohomologous E' (hclasses E.factorSet E'.factorSet hc hE')⟩

/-- For the twelve-orbit quotient action, the specified elementary kernel has
a complement in the actual involution centralizer. -/
public theorem twelveOrbit_complement
    (haction : ActionEquivalent D.quotientBinaryAction twelveOrbitAction) :
    ∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K :=
  twelveOrbit_complement_of_cocycle_vanishing D twelveOrbit_isCoboundary haction

/-- For the six-orbit quotient action, the specified elementary kernel has a
complement or the centralizer is isomorphic to the exact third permutation model. -/
public theorem sixOrbit_alternatives
    (haction : ActionEquivalent D.quotientBinaryAction sixOrbitAction) :
    (∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K) ∨
      Nonempty (D.centralizer ≃* NonsplitModels.Third) :=
  sixOrbit_alternatives_of_cocycle_classification D
    sixOrbit_cohomologous_of_not_isCoboundary third_nonsplit_realization haction

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions

module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Noninner
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData
public import Theory.GroupTheory.GeneralizedFitting.IndexTwoCoverTransport
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Assembly of the concrete Held outer fixed-subgroup calculation

There are two independent finite-group obligations: the `3.A₇.2` structure
of the explicit representative's fixed subgroup, and conjugacy coverage
of all outer involutory actions induced by the full permutation normalizer.
An actual fixed-subgroup isomorphism then transports the covering subgroup.

Both obligations remain explicit here. The source row is not established
until both are discharged. In particular, coverage concerns the order of
the induced action, with no assumption on the implementing permutation's
order. Source: GLS3 Table 5.3p and its interpretation on pp.260–261.
-/

public section

open Subgroup Theory.GroupTheory
namespace Held.OuterInvolution

/-- Assemble the source row from a representative calculation and genuine
conjugacy coverage of the implemented automorphisms. -/
theorem outerRow_of_representative
    (hfixed : HasQuasisimpleNormalOfIndexTwo action.fixedSubgroup 3)
    (hconj : ∀ n : normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))),
      orderOf (permutationGroup.normalizerMonoidHom n) = 2 →
      (¬ ∃ g : He, MulAut.conj g = permutationGroup.normalizerMonoidHom n) →
      ∃ g : He, MulAut.congr (MulAut.conj g) action =
        permutationGroup.normalizerMonoidHom n) : InvolutionFixedData.OuterRow := by
  intro n hn hout
  obtain ⟨g, hg⟩ := hconj n hn hout
  rw [← hg]
  exact hfixed.of_mulEquiv (MulAut.fixedSubgroupCongr (MulAut.conj g) action)

end Held.OuterInvolution

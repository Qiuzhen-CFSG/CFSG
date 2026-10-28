module

public import Theory.SpecificGroups.Held.Automorphisms.Reduction
public import Theory.GroupTheory.CyclicNormalOddQuotient

/-!
# Reduction of the Held outer restriction to concrete model calculations

Theorem C includes Held's group (Aschbacher–Smith, printed p.33).
The inspection on p.510 follows from its two-group outer automorphism group,
as recorded in GLS3, Table 5.3p.

For the fixed degree-2058 construction, the proof below combines realization
of every automorphism by the permutation normalizer with a two-group bound
on its quotient by Held. Both premises remain separate proof obligations;
the source theorem is not yet established. Transport uses an actual group
isomorphism and the induced isomorphism of full outer automorphism groups.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels

open Theory.GroupTheory

/-- Conditional assembly from the two independent concrete-model obligations.
The Held source case remains open until both premises have been proved. -/
theorem held_model_outer_cyclicNormalOddQuotient_of_permutation_normalizer
    {S : Type*} [Group S] (e : S ≃* Held.He)
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (htwo : IsPGroup 2 Held.PermutationNormalizerQuotient) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  have houter : IsPGroup 2 (MulAut.Outer Held.He) :=
    Subgroup.isPGroup_outer_of_normalizer Held.permutationGroup 2 hreal htwo
  exact (hasCyclicNormalOddQuotient_of_isPGroup_two houter).of_injective
    (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels

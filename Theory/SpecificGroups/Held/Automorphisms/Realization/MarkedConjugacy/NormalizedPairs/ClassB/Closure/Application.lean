module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound
public import Theory.SpecificGroups.Held.Automorphisms.Realization

/-!
# Unconditional realization of automorphisms of the original Held carrier

The completed second-class closure certificate combines with its checked
relator rejections and the completed first-class calculation. The original
normalized pairs consequently fix a marked point. The proved Sylow-seventeen
and marked-subgroup index calculations then give inner conjugacy of the marked
subgroup and realize every automorphism in the full permutation normalizer.

Source: the retained ATLAS HeG1-P1.M and HeG1-p2058B0 generators and marked
subgroup, as used for the Held automorphism group in GLS3, Table 5.3p.
-/

namespace Held.Realization.MarkedConjugacy.NormalizedPairs

/-- The second whole involution-class calculation, with every row discharged. -/
public theorem classCalculation_secondSeed : ClassCalculation secondSeed :=
  ClassB.classCalculation_of_closure ClassB.closedAt_all

/-- Every original normalized generator pair has the required common fixed point. -/
public theorem normalizedPairFixedPoint : NormalizedPairFixedPoint :=
  normalizedPairFixedPoint_of_classCalculations classCalculation_a classCalculation_secondSeed

end Held.Realization.MarkedConjugacy.NormalizedPairs

namespace Held.Realization

/-- Every automorphism preserves the conjugacy class of the literal marked subgroup. -/
public theorem markedSubgroup_map_conjugate (f : MulAut He) :
    ∃ g : He, markedSubgroup.map f.toMonoidHom =
      markedSubgroup.map (MulAut.conj g).toMonoidHom :=
  MarkedConjugacy.map_conjugate_of_calculations markedSubgroup_index_le
    MarkedConjugacy.seventeen_cyclic_index_not_dvd
    MarkedConjugacy.NormalizedPairs.normalizedPairFixedPoint f

/-- The full permutation normalizer realizes every automorphism of the
concrete Held group, without any remaining certificate premise. -/
public theorem normalizer_surjective :
    Function.Surjective permutationGroup.normalizerMonoidHom :=
  normalizer_surjective_of_markedSubgroup markedSubgroup_index_le markedSubgroup_map_conjugate

end Held.Realization

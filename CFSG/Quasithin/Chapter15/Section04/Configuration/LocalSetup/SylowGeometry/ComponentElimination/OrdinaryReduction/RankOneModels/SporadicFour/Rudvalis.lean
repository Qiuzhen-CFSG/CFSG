module

public import Theory.SpecificGroups.Rudvalis.Model.ElementaryFive

/-!+# The Rudvalis odd-subgroup witness

The actual degree-4060 permutation carrier contains the explicitly certified
elementary abelian subgroup of order 25. This supplies the five-subgroup
premise consumed by `sporadic_four_separation_of_subgroups`.

Source: Aschbacher–Smith, full 1.1.5(3)(f), printed pp.501–503, compared
with the proof of 15.4.20, printed p.1164. The concrete witness and its
ATLAS attribution are in `Theory.SpecificGroups.Rudvalis.Model.ElementaryFive`.
-/

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels

/-- The concrete Rudvalis carrier contains a noncyclic five-subgroup. -/
public theorem rudvalis_noncyclic_five_subgroup :
    ∃ P : Subgroup Rudvalis.Model, IsPGroup 5 P ∧ ¬ IsCyclic P :=
  ⟨Rudvalis.ElementaryFive.subgroup,
    Rudvalis.ElementaryFive.subgroup_pGroup_and_not_cyclic⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels

module

public import GorensteinWalter.ComponentLayerConjugate
public import GorensteinWalter.FittingSubgroupConjugate

/-!
# Conjugation transport for generalized Fitting subgroups

This combines the Fitting-subgroup and component-layer transport theorems.
-/

namespace GorensteinWalter

universe u

noncomputable section

/-- Conjugating a subgroup conjugates its generalized Fitting subgroup. -/
public theorem generalizedFittingSubgroupOf_conjugateSubgroup
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (g : G) :
    generalizedFittingSubgroupOf (conjugateSubgroup A g) =
      (generalizedFittingSubgroupOf A).map (MulAut.conj g).toMonoidHom := by
  rw [generalizedFittingSubgroupOf, generalizedFittingSubgroupOf,
    fittingSubgroupOf_conjugateSubgroup, componentLayerOf_conjugateSubgroup,
    Subgroup.map_sup]

end

end GorensteinWalter

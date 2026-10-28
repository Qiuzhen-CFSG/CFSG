module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_6

/-!
Existence of a maximal torus in the standard special linear variety.  The
general maximal-torus existence theorem applies because the determinant-one
locus carries its algebraic-group structure over an algebraically closed field.
-/

set_option warningAsError false

universe u

namespace Theory.AlgebraicGroup

public theorem slVariety_exists_standard_maximalTorus
    {k : Type u} [Field k] [IsAlgClosed k] (m : ℕ) :
    ∃ T : ClosedSubgroup (slVariety k (m + 1)),
      IsMaximalTorus T := by
  exact exists_maximalTorus (slVariety k (m + 1))

end Theory.AlgebraicGroup

module

public import Theory.SpecificGroups.Monster.Construction.QuasithinObstruction.Projection
public import Theory.SpecificGroups.Monster.Construction.QuasithinObstruction.SpinLift
public import Theory.SpecificGroups.Monster.Construction.QuasithinObstruction.LatticeRank

/-!
# The local quotient for the Monster quasithin obstruction

The actual spin–Leech tensor image surjects onto the lattice Leech central
quotient. Its embedding in the fixed Griess carrier centralizes the
specified involution. The projection retains its lattice representative
and the source N₁ equations; it kills the distinguished local involution.
Orthogonal quarter turns give the surjectivity, and the explicit icosian
and alternating product supplies rank at least three in the target.
This narrow interface does not require the reverse centralizer containment
or the full triality action.

Source: Aschbacher, *Sporadic Groups*, 27.5–27.9 and 28.12–28.13;
Aschbacher–Smith, A.2.15(2) and A.2.19.
-/

public section
namespace Sporadic.Monster.Construction.QuasithinObstruction

/-- The literal embedded local subgroup surjects onto the lattice Conway quotient. -/
theorem localToLeechQuotient_surjective : Function.Surjective localToLeechQuotient :=
  cToLeechQuotient_surjective.comp cEquivLocalSubgroup.symm.surjective

end Sporadic.Monster.Construction.QuasithinObstruction

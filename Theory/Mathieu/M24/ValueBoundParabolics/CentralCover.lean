module

public import Theory.Mathieu.M24.ValueBoundParabolics.CentralCover.PrimeReduction
public import Theory.Mathieu.M24.ValueBoundParabolics.CentralCover.ThreeLocalData
public import Theory.Mathieu.M24.ValueBoundParabolics.CentralCover.ThreeTransfer
public import Theory.Mathieu.M24.ValueBoundParabolics.CentralCover.ThreeModel

/-!
# Central covers of M₂₄ with trivial two-core

For a finite quasisimple group with central quotient isomorphic to the actual
Witt-design M₂₄, a trivial two-core forces the center to be trivial. Cyclic
Sylow transfer excludes all primes other than two and three from the center,
and the two-core hypothesis excludes two. The certified inverted Heisenberg
Sylow three-subgroup of M₂₄ supplies the local configuration that excludes
three from the kernel of the perfect central quotient cover. Thus every
prime is excluded from the center, proving its triviality.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.4.3(2), printed pp.241--242, and I.1.1--I.1.4, printed pp.407--408.
-/

public section

open Subgroup Theory.GroupTheory PerfectCentralCovering

namespace Sporadic.Mathieu.M24ValueBoundParabolics

variable {X : Type*} [Group X] [Finite X] [IsQuasisimple X]

/-- A finite quasisimple group with trivial two-core and actual central quotient
M₂₄ has trivial center. -/
theorem center_eq_bot_of_twoCore_eq_bot
    (hcore : pCore 2 X = ⊥) (e : X ⧸ center X ≃* M24) : center X = ⊥ := by
  apply center_eq_bot_of_twoCore_eq_bot_of_three_not_dvd hcore e
  rw [← centralQuotientCover_ker e]
  exact not_three_dvd_kernel_of_invertedHeisenbergSylow
    (centralQuotientCover e) invertedHeisenbergSylowThree

end Sporadic.Mathieu.M24ValueBoundParabolics

end

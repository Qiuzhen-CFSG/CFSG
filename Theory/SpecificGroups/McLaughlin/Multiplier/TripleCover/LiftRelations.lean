module

public import Theory.SpecificGroups.McLaughlin.Multiplier.TripleCover.Presentation
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Local matrix identities for a McLaughlin triple cover

The candidate matrices are the ATLAS `3McLG1-f25r45aB0` generators.
Their distinguished scalar word is `(AB)^11`. The explicit conditions below
are finite word identities and centrality in the ambient matrix-unit group.
They do not assume a covering, perfectness, or identification of a quotient.

`TripleCover.lean` constructs the paired group and proves those conclusions
from these identities and a complete marked presentation of the base.
Certification of the candidate matrices remains a separate obligation.
See `source/README.md` for the original data, conventions, and attribution.
-/

namespace Theory.SpecificGroups.McLaughlin.Multiplier.TripleCover

/-- The lift of the eleventh-power relator of the standard product. -/
@[expose] public def scalar {H : Type*} [Group H] (A B : H) : H := (A * B) ^ 11

/-- Finite word checks for two proposed lift generators. These must be proved
on actual matrices; no presentation-completeness claim is part of this record. -/
public structure LiftRelations {H : Type*} [Group H] (A B : H) : Prop where
  a_sq : A ^ 2 = 1
  b_fifth : B ^ 5 = 1
  ab_pow : (A * B) ^ 33 = 1
  scalar_central : scalar A B ∈ Subgroup.center H
  scalar_ne_one : scalar A B ≠ 1
  relators_cyclic : ∀ w ∈ relators, evaluate A B w ∈ Subgroup.zpowers (scalar A B)

end Theory.SpecificGroups.McLaughlin.Multiplier.TripleCover

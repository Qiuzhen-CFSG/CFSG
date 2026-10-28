module

public import CFSG.Quasithin.ClassicalModels

/-!
# The conclusion of Theorem 13.5.12

The alternatives retain the degree of the original alternating action.
The group predicates assert isomorphisms with actual projective matrix
carriers; in particular U₄(q) uses matrices over a field of order q².
No recognition assertion is part of this definition.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Theorem 13.5.12, printed p.918 (PDF p.935).
-/

namespace CFSG.Quasithin.Chapter13.Section05

/-- Exactly the two numbered conclusions of source Theorem 13.5.12. -/
@[expose] public def ModelConclusion (G : Type*) [Group G] (n : ℕ) : Prop :=
  (n = 5 ∧ (ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3)) ∨
    (n = 6 ∧ ClassicalGroup.IsPSU G 4 3)

end CFSG.Quasithin.Chapter13.Section05

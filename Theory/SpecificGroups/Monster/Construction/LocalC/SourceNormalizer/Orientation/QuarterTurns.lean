module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.Extraspecial

/-!
# Quarter-turn automorphisms of the actual extraspecial spin group

For an element `q` whose square is the central involution, the corresponding
quarter turn fixes elements commuting with `q` and sends every other `x` to
`q * x`. In the real spin representation this is conjugation by `1 + ρ(q)`;
on the central quadratic quotient it is the symmetry in the nonsingular
vector represented by `q`.

This module specifies the generating family on the actual group `Q1Image`.
It does not assume or assert that the family generates its automorphism group.
The orientation reduction uses precisely that separate generation statement.

Source: Aschbacher, *Sporadic Groups*, Section 14, Exercise 4.4, printed
p. 64, and the spin normalizer on printed pp. 147–148.
-/

@[expose] public section
namespace Sporadic.Monster.Construction.LocalC.SourceNormalizer
open TrialitySpin

/-- The automorphisms implemented by extraspecial quarter turns. -/
def quarterTurnAutomorphisms : Set (MulAut Q1Image) :=
  {α | ∃ q : Q1Image, q ^ 2 = q1ImageCenterGenerator ∧
    ∀ x : Q1Image, (Commute q x → α x = x) ∧ (¬ Commute q x → α x = q * x)}

end Sporadic.Monster.Construction.LocalC.SourceNormalizer

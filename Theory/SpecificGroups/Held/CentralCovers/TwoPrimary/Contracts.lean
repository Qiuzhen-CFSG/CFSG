module

public import Theory.SpecificGroups.Held.Model.Presentation
public import Mathlib.GroupTheory.IsPerfect

/-!
# Binary defects in the Held relators

This is the explicit relator calculation needed by the presentation route to
the two-primary multiplier bound. A lift of the two standard generators to a
perfect central double extension satisfies each of the seven relators up to
the same central involution. The required calculation removes all seven defects by
changing the two lifts by that involution.

The proposition below is a contract, not an established model fact. Its
construction and injectivity of `Held.presentationMap` are independent inputs
to the conditional assembly. The ATLAS file's informal identification of its
presentation uses the trivial Held multiplier and cannot discharge either
input in this application.

Source of the exact words: John Bray, ATLAS `HeG1-P1`, retained verbatim in
`Theory/SpecificGroups/Held/Model/Source/HeG1-P1.M`.
-/

namespace Held.CentralCovers.TwoPrimary

universe u

/-- The seven binary central relator defects can be removed by changing the
two generator lifts. This retains the actual words and a single central
involution common to all defects. -/
@[expose] public def BinaryRelatorLifting : Prop :=
  ∀ (E : Type u) [Group E] [Finite E] [Group.IsPerfect E] (z x y : E),
    z ∈ Subgroup.center E → z ^ 2 = 1 →
    (∀ i : Fin 7, relationWord x y i = 1 ∨ relationWord x y i = z) →
    ∃ ε η : Fin 2,
      ∀ i : Fin 7, relationWord (x * z ^ ε.val) (y * z ^ η.val) i = 1

end Held.CentralCovers.TwoPrimary

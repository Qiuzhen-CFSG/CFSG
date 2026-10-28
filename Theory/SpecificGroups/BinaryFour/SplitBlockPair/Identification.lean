module

public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Identification.Orbit
public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Identification.Joined
public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Identification.Stabilizer

/-!
# Identifications for the compatible binary pair

The local C₂ × S₃ and A₄ equivalences, their common embedded four-group,
and compatibility with the marked evaluation action are proved in `Locals`.
`Orbit` proves transitivity on the fifteen nonzero vectors and the precise
orbit–stabilizer cardinality relation.
`Joined` identifies the literal join with A₇ through the exceptional A₈ action.
Here that equivalence discharges the sole extra premise of `Stabilizer`, giving
the unconditional PSL₃(2) identification of the stabilizer of `(0,1,0,0)`.
Its map is the faithful action on the quotient by the marked line, followed
by the canonical binary linear/projective comparison. The imported action
equations retain the original embeddings and evaluation action on E₁₆.

This completes the concrete GL₄(2) calculation. Realizing the pair by the
ambient source subgroups is a separate split-block argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 14.4.4, printed p.1007.
-/

namespace BinaryFourSplitPair

/-- The actual evaluation stabilizer of the marked vector is PSL₃(2).
The joined-group premise of the quotient-action construction is discharged
by the exceptional-action identification. -/
public noncomputable def pointStabilizerEquiv :
    MulAction.stabilizer joined point ≃* Matrix.PSL3Two.PSL :=
  pointStabilizerEquivOfAlternating joinedEquivAlternating

/-- The literal marked-line quotient action is faithful, unconditionally. -/
public theorem pointStabilizerQuotientAction_injective :
    Function.Injective pointStabilizerQuotientAction :=
  pointStabilizerQuotientAction_injective_of_alternating joinedEquivAlternating

/-- The order of the joined group follows from its genuine A₇ identification. -/
public theorem joined_card : Nat.card joined = 2520 := by
  rw [Nat.card_congr joinedEquivAlternating.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.card_fin, Nat.factorial]

/-- The order of the marked stabilizer follows from its genuine PSL₃(2) identification. -/
public theorem pointStabilizer_card :
    Nat.card (MulAction.stabilizer joined point) = 168 := by
  rw [Nat.card_congr pointStabilizerEquiv.toEquiv, Matrix.PSL3Two.card_PSL]

end BinaryFourSplitPair

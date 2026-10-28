module

public import Theory.SpecificGroups.AlternatingSix.M10.Action.SylowTransport
public import Theory.SpecificGroups.AlternatingSix.M10.Action.DegreeTen

/-!
# Assembly of the concrete M₁₀ action facts

The extension's normality, order, nine-group containment and exclusion of
transpositions are proved in `Action.Extension`. `Action.SylowTransport`
identifies the literal normalizer quotient with its Sylow three-subgroup
action, and supplies the stabilizer order and double-coset deductions.

`Action.DegreeTen` proves that this Sylow action has degree ten and is
three-transitive, using the actual exceptional generator. The final theorem
`actionFacts` discharges both finite-action premises for every subgroup of S₆
of order nine. It supplies the action input to the source consumer
`SymmetricNormalizerData.m10GeometryOfModelFacts`.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), following 4.8 and the action used in 4.10, pp.41–42.
-/

public section
namespace AlternatingSix.M10
open Subgroup Action

/-- The finite Sylow action calculation supplies all fields of the source contract. -/
theorem actionFacts_of_sylowAction
    (hc : Nat.card (Sylow 3 extension) = 10)
    (ht : MulAction.IsMultiplyPretransitive extension (Sylow 3 extension) 3)
    (D : Subgroup (Equiv.Perm (Fin 6))) (hD : Nat.card D = 9) : ActionFacts D := by
  have hquot := quotient_threeTransitive_of_sylow ht D hD
  have htwo : MulAction.IsMultiplyPretransitive extension
      (extension ⧸ (stabilizer D).subgroupOf extension) 2 := by
    let := hquot
    apply MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 3)
    rw [card_quotient_of_card_sylow hc D hD]
    decide
  exact ⟨extension_normal, card_extension, nine_le_extension D hD,
    swap_not_mem_extension, card_stabilizer_of_card_sylow hc D hD,
    hquot, doubleCoset_cover_of_twoTransitive D htwo⟩

/-- The specified M₁₀ extension has all the required action properties for
every nine-group in the natural S₆. In particular, three-transitivity is on
the literal normalizer quotient, and the double-coset cover holds for every
representative outside that normalizer. -/
theorem actionFacts (D : Subgroup (Equiv.Perm (Fin 6))) (hD : Nat.card D = 9) :
    ActionFacts D :=
  actionFacts_of_sylowAction card_sylowThree sylowThree_threeTransitive D hD

end AlternatingSix.M10

module

public import Stellmacher.Recognition.FongWreathedBorelAction
public import Stellmacher.Recognition.FongWreathedBorelSubgroups

/-!
# Fong's Borel subgroup and faithful degree-28 action

The supplied character data and the local wreathed-Sylow hypotheses construct
an actual element `R` of order three and subgroups `Q` and `B`. The subgroup
`Q` has order 27 and is normal in `B`, whose quotient by `Q` is cyclic of
order eight. The coset action on `G/B` is faithful and doubly transitive;
its character is `1 + chi 1`, and `Q` is regular away from the identity coset.

The construction combines the local centralizer and odd-core arguments with
column orthogonality and the fixed-point interpretation of the permutation
character. `BorelAction` packages the actual subgroup and action witnesses
for the later Suzuki recognition step. Its existence theorem assumes only
the local group hypotheses and `CharacterData`, with no action assumption.
The elementary subgroup consequences remain re-exported under their original
public names.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization
of U(3,3)*, J. Algebra 6 (1967), equation (10), p.73, and pp.74–75.
-/

namespace Stellmacher.Recognition.FongWreathed

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
variable (P : ABG.Wreathed.Presentation S 2)

/-- Actual Borel subgroups and their coset action, ready for recognition.
Normality, the order-216 stabilizer, and its cyclic order-eight quotient are
available from `subgroups.normal_Q_in_B`, `subgroups.card_B`,
`subgroups.quotient_cyclic`, and `subgroups.card_quotient`. -/
public structure BorelAction (c : CharacterData P) where
  subgroups : BorelSubgroups P
  degree : Nat.card (G ⧸ subgroups.B) = 28
  faithful : FaithfulSMul G (G ⧸ subgroups.B)
  doubly_transitive : MulAction.IsMultiplyPretransitive G (G ⧸ subgroups.B) 2
  character : subgroups.cosetRepresentation.character = 1 + c.chi 1
  regular : ∀ x y : G ⧸ subgroups.B,
    x ≠ subgroups.baseCoset → y ≠ subgroups.baseCoset →
      ∃! q : subgroups.Q, (q : G) • x = y

/-- Fong's degree-28 construction from the complete supplied character
contract. In particular, the Borel subgroups and the action are conclusions,
not hypotheses of this implication. -/
public theorem nonempty_borelAction [IsSimpleGroup G]
    (hS : ABG.IsWreathedOfHeight S 2) (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))]
    (hG : Nat.card G = 6048) (c : CharacterData P) :
    Nonempty (BorelAction P c) := by
  obtain ⟨b⟩ := nonempty_borelSubgroups P hS x hx hG c
  have hCF := card_centralizer_F P hS x hx hG c
  exact ⟨{
    subgroups := b
    degree := b.card_cosets hG
    faithful := b.faithful_cosets hG
    doubly_transitive := b.cosetAction_two_pretransitive c hG hCF
    character := b.cosetRepresentation_character c hG hCF
    regular := b.Q_regular_off_base c hG hCF
  }⟩

end Stellmacher.Recognition.FongWreathed

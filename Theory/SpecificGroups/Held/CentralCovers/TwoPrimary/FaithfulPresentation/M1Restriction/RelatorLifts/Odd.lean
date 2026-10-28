module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.RelatorLifts.Conjugates
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.RelatorLifts.Odd.Consequences
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.RelatorLifts.Odd.Torus

/-!
# Reduction of the odd M₁ relations to entry 7

Source reflection reduces entry 8 to entry 7. The explicit word derivation in
`Odd.Consequences` reduces entry 9 to entry 7 and the four allowed even words.
The remaining source obligation is entry 7 itself. In particular, the theorem
below is conditional and is not `odd_lifted_relations`.
The independent source calculation in `Odd.Torus` proves that the common
five-letter shifted word commutes with `y` and has seventh power one.

Sources: John Bray's `Held/Model/Source/HeG1-P1.M` and the frozen marked words
in `M1Restriction/Data.lean`.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction

/-- The odd branch is reduced to entry 7, with the original even premises. -/
theorem odd_lifted_relations_of_seven
    (hEven : ∀ i : Fin 12, (i = 4 ∨ i = 6 ∨ i = 10 ∨ i = 11) →
      Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters i) = 1)
    (hSeven : Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters 7) = 1) :
    ∀ i : Fin 12, (i = 7 ∨ i = 8 ∨ i = 9) →
      Subgroup.CosetWordCertificate.eval liftedGenerator (relationLetters i) = 1 := by
  intro i hi
  rcases hi with rfl | rfl | rfl
  · exact hSeven
  · exact RelatorLifts.relation_eight_of_seven hSeven
  · exact RelatorLifts.relation_nine_of_even_and_seven hEven hSeven

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction

module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.Contracts
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.Normalization
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.RemainingDefects
import Mathlib.Tactic.FinCases

/-!
# Assembly of binary relator lifting for Held

The proved normalization removes the seventh- and seventeenth-power defects
and proves the long commutator relation. The checked even and remaining-defect
calculations remove the square, sixth-power, fifth-power and final-word
defects, so this module establishes `BinaryRelatorLifting` outright.

Source: the seven literal words of John Bray's ATLAS `HeG1-P1`, retained in
`Held/Model/Source/HeG1-P1.M`. The source's multiplier-based identification of
the presentation is not used.
-/

namespace Held.CentralCovers.TwoPrimary

universe u

/-- The remaining two word calculations suffice for the exact published
contract. The second calculation may use the first one's two conclusions;
this assembly supplies both, and supplies the normalized input itself. -/
public theorem binaryRelatorLifting_of_remaining_defects
    (heven : ∀ (E : Type u) [Group E] [Finite E] [Group.IsPerfect E] (z x y : E),
      BinaryRelators.Normalized z x y →
        relationWord x y 0 = 1 ∧ relationWord x y 5 = 1)
    (hremaining : ∀ (E : Type u) [Group E] [Finite E] [Group.IsPerfect E] (z x y : E),
      BinaryRelators.Normalized z x y →
        relationWord x y 0 = 1 → relationWord x y 5 = 1 →
        relationWord x y 4 = 1 ∧ relationWord x y 6 = 1) :
    BinaryRelatorLifting.{u} := by
  intro E _ _ _ z x y hz hs hr
  obtain ⟨ε, η, hn⟩ := BinaryRelators.normalize z x y hz hs hr
  obtain ⟨h0, h5⟩ := heven E z _ _ hn
  obtain ⟨h4, h6⟩ := hremaining E z _ _ hn h0 h5
  refine ⟨ε, η, ?_⟩
  intro i
  fin_cases i
  · exact h0
  · exact hn.seventh
  · exact hn.seventeenth
  · exact hn.long_commutator
  · exact h4
  · exact h5
  · exact h6

/-- The seven binary central defects can always be removed for finite perfect
Held lifts. Normalization supplies the odd-power and long-commutator
relations, while the checked even and remaining-defect calculations discharge
the four residual words. -/
public theorem binaryRelatorLifting : BinaryRelatorLifting.{u} := by
  apply binaryRelatorLifting_of_remaining_defects
  · intro E _ _ _ z x y h
    exact BinaryRelators.even_defects E z x y h
  · intro E _ _ _ z x y h h0 h5
    exact BinaryRelators.remaining_defects E z x y h h0 h5

end Held.CentralCovers.TwoPrimary

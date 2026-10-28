module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.Normalization
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.RemainingDefects.Centralizer
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.RemainingDefects.CosetMembership
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects

/-!
# Elimination of the two remaining Held defects

The centralizer calculation and its checked subgroup-membership certificate
eliminate the fifth-power defect, using the exact square and sixth-power
relations. The independent central-tail calculation in `EvenDefects` eliminates
the final-word defect from the normalized source relations alone. Together
these prove `remaining_defects` with no further premises.

The conditional assembly is retained for callers supplying their own two
calculations; it allows the final-word calculation to use the fifth-power relation.
The source is John Bray's ATLAS `HeG1-P1.M`, retained in `Held/Model/Source/`;
its presentation identification and multiplier claims are not used.
-/

namespace Held.CentralCovers.TwoPrimary.BinaryRelators

universe u

/-- The two separate calculations suffice for the exact remaining-defects
contract. The final-word calculation receives the proved fifth-power relation. -/
public theorem remaining_defects_of_centralizer_and_final_word
    (hmember : ∀ (E : Type u) [Group E] (z x y : E),
      Normalized z x y → relationWord x y 0 = 1 → relationWord x y 5 = 1 →
        RemainingDefects.centralizerWord x y ∈ RemainingDefects.centralizerSpan z x y)
    (hfinal : ∀ (E : Type u) [Group E] [Finite E] [Group.IsPerfect E] (z x y : E),
      Normalized z x y → relationWord x y 0 = 1 → relationWord x y 5 = 1 →
        relationWord x y 4 = 1 → relationWord x y 6 = 1)
    (E : Type u) [Group E] [Finite E] [Group.IsPerfect E] (z x y : E)
    (h : Normalized z x y) (h0 : relationWord x y 0 = 1)
    (h5 : relationWord x y 5 = 1) :
    relationWord x y 4 = 1 ∧ relationWord x y 6 = 1 := by
  have h4 := RemainingDefects.fifth_eq_one_of_membership z x y h h0 h5
    (hmember E z x y h h0 h5)
  exact ⟨h4, hfinal E z x y h h0 h5 h4⟩

/-- The fifth-power and final-word relators are exact once the square and
sixth-power relators are exact. Both certificate premises are discharged. -/
public theorem remaining_defects
    (E : Type u) [Group E] [Finite E] [Group.IsPerfect E] (z x y : E)
    (h : Normalized z x y) (h0 : relationWord x y 0 = 1)
    (h5 : relationWord x y 5 = 1) :
    relationWord x y 4 = 1 ∧ relationWord x y 6 = 1 := by
  have h4 := RemainingDefects.fifth_eq_one_of_membership z x y h h0 h5
    (RemainingDefects.centralizerWord_mem z x y h h0 h5)
  exact ⟨h4, EvenDefects.final_defect_eq_one z x y h⟩

end Held.CentralCovers.TwoPrimary.BinaryRelators

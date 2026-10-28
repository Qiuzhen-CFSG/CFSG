module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.MainNormalization

/-!
# Applying the proved main-coordinate normalization

The checked first-block conjugation discharges the `MainNormalization`
premise of the existing outside-C consumer. The separate square-coordinate
calculation remains explicit and is discharged by the involution-branch
assembly owner.

Source: GLS3 Table 2.4 and 2.4.5(d), refs/KGroup/GLS3/chapter2.tex;
Guralnick--Malle Lemma 8.8, internal p.57.
-/

public section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses
open OutsideC

/-- The outside-C branch now needs only its separate square-coordinate calculation. -/
theorem outsideCConjugacy_of_squarePruning (m : ℕ) (hsquare : SquarePruning m) :
    OutsideCConjugacy m :=
  outsideCConjugacy_of_coordinate_calculations m hsquare (mainNormalization m)

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses

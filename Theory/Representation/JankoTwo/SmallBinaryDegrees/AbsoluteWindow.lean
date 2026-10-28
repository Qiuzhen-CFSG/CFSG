module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.Calculations
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.Contracts
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.TracePowers
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.SixTrace

/-!
# A power-fusion route to the small Hall--Janko trace field

Conjugacy of the eighth and thirty-second powers in the literal degree-100
carrier would put every characteristic-two character value in the quadratic
fixed field. The trace-power theorem proves this implication without a degree
or irreducibility assumption.

The degree-six nonbinary trace witness is proved by Frobenius descent and the
binary faithful-degree obstruction. Degree completeness, power fusion, and the
degree-fourteen nonbinary trace witness remain explicit inputs specified in
`AbsoluteWindow/Contracts.lean`. The final theorem is a conditional assembly,
not the completed modular representation catalogue.

Sources: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
manuscript p.16, and Hiss--Malle, corrected Table 2, the characteristic-two
J₂ entries of degrees 6 and 14 with field b5.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow

open Sporadic.LeechRelated.J2
universe v

/-- Actual carrier power fusion suffices for the upper trace-field bound in
every dimension and over every characteristic-two field. -/
theorem character_four_of_fusion (hfusion : PowerFusion)
    {K U : Type*} [Field K] [CharP K 2] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (τ : Representation K Carrier U) (g : Carrier) :
    τ.character g ^ 4 = τ.character g := by
  exact character_four_of_power_fusion τ g 3 (by simpa using hfusion g)

/-- Assemble the exact source calculation once the independent degree,
power-fusion and nonbinary-trace obligations have all been discharged. -/
theorem calculations_of_degree_fusion_separation
    (hdegree : DegreeWindow.{v}) (hfusion : PowerFusion)
    (hseparation : TraceSeparation.{v}) : AbsoluteWindowCalculations.{v} := by
  intro K _ _ _ U _ _ _ τ hf hi hd
  have hdegrees := hdegree K U τ hf hi hd
  exact ⟨hdegrees, character_four_of_fusion hfusion τ,
    hseparation K U τ hf hi hdegrees⟩

/-- The degree-six trace calculation is discharged. The exact absolute window
now needs only degree completeness, carrier power fusion, and the degree-fourteen
nonbinary trace calculation. -/
theorem calculations_of_degree_fusion_fourteen
    (hdegree : DegreeWindow.{v}) (hfusion : PowerFusion)
    (hfourteen : FourteenTraceSeparation.{v}) : AbsoluteWindowCalculations.{v} :=
  calculations_of_degree_fusion_separation hdegree hfusion (traceSeparation_of_fourteen hfourteen)

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow

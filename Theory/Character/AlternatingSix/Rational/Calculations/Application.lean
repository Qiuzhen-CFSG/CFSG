module

public import Theory.Character.AlternatingSix.Rational
public import Theory.Character.AlternatingSix.Rational.Calculations

/-!
# Rational A6 characters from the checked permutation calculations

The concrete `permutationCalculations` discharges the finite-calculation premise
of the rational-character constructor. Only the independent separation of the
two order-three classes remains explicit; its producer and unconditional
assembly belong to the order-three and rational-character constructions.

Source: Janko, *A characterization of the Mathieu simple groups, I*, Section 6,
pp.10–11, the four rational rows inflated from A6.
-/

namespace Theory.Character.AlternatingSix.RationalConstruction

/-- Apply the checked finite calculations to the actual rational-block consumer.
The sole remaining premise is conjugacy separation in A6, not character data. -/
public theorem rationalBlock_of_otherThreeSeparation (separation : OtherThreeSeparation)
    (c : A6) (hc : orderOf c = 3) : Nonempty (RationalBlock c) :=
  rationalBlock_of_permutation_calculations permutationCalculations separation c hc

end Theory.Character.AlternatingSix.RationalConstruction

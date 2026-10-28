module

public import Theory.Character.AlternatingSix.Rational
public import Theory.Character.AlternatingSix.Rational.ThreeClasses

/-!
# Applying the A6 order-three class separation

The proved conjugacy separation discharges the marking premise of
`rationalBlockOfPermutationCalculations`, for the literal natural six-letter
action. The only remaining input is the independent integer row calculation
record; construction of that record belongs to the rational-character assembly.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
Section 6, pp.10–11, rows χ₂, χ₃, χ₆, χ₇.
-/

namespace Theory.Character.AlternatingSix

open RationalConstruction

/-- The permutation calculations alone now suffice for the rational block:
the A6 conjugacy marking has been proved in `otherThreeSeparation`. -/
public theorem rationalBlock_of_row_calculations (D : PermutationCalculations)
    (c : alternatingGroup (Fin 6)) (hc : orderOf c = 3) :
    Nonempty (RationalBlock c) :=
  ⟨rationalBlockOfPermutationCalculations D otherThreeSeparation c hc⟩

end Theory.Character.AlternatingSix

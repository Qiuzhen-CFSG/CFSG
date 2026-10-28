module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Calibration.Differences
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Calibration.Columns
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Calibration.ExpressionColumns
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Calibration.Initial
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Calibration.Orbit
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Calibration.Inverse
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Calibration.Small
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Calibration.Equations
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Reduction

/-!
# Literal calibration and exhaustive orbit certificates for the max4 commutant

The eight unconditional families exported here establish the difference and
transpose tables, the initial rows, every orbit recurrence, the inverse, and
the selected commutator equations. All arithmetic certificates are checked by
the Lean kernel against the unchanged `Commutant.Tables` witnesses.

`CommutantProof.lowerTriangular_of_checks` consumes precisely these families,
together with the independent pivot and upper-entry elimination certificates.
Final commutant assembly belongs to the parent module; calibration does not
assume that an arbitrary commuting matrix is triangular.

Source and conventions: `Commutant/source/README.md` and
`CharacteristicTwo/source/reconstruction.json`. Checker measurements and
regeneration instructions are in `Calibration/source/README.md`.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof

/-- Apply all eight calibration families to the exact eleven-matrix consumer.
Only the independent pivot and upper-entry certificates remain explicit. -/
theorem lowerTriangular_of_elimination_checks
    (hp : ∀ t, PivotCheck t) (hu : ∀ i, UpperCheck i)
    (M : BinaryMatrix)
    (hM : ∀ a : Fin 11, Commute M (decodeRows (Coordinates.conjugateRows.get a))) :
    ∀ i j : Fin 112, i < j → M i j = 0 :=
  lowerTriangular_of_checks differences_checked columns_checked expressionColumns_checked
    initial_checked orbit_checked inverse_checked small_checked equations_checked hp hu M hM

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof

module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Calibration
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Elimination

/-!
# The lower-triangular commutant of the eleven literal max4 matrices

Commutation determines every matrix entry from the last four rows by the
certified orbit recurrences and inverse. The selected commutator equations
vanish on these 448 entries; the checked elimination expresses every strictly
upper entry as a combination of those equations. `Calibration` and `Elimination`
prove all ten numerical families consumed by `CommutantProof.lowerTriangular_of_checks`.
Thus the bound applies to all binary matrices, including singular matrices.

`commuting_matrices_lowerTriangular` has only the eleven commutation premises,
with no group, invertibility, or numerical-certificate hypothesis. Its application is
`centralizer_seedNormalClosure_isPGroup_of_matrix_certificates` in the separate
CharacteristicTwo assembly, which this independent branch does not import.

Source: `CharacteristicTwo/source/README.md`, and Aschbacher–Smith condition E,
printed pp.3–4 and 481–482. See `Commutant/source/README.md` for the witness
contracts and measured kernel checks.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo

/-- Every binary matrix commuting with the eleven published tables is lower
triangular. All reconstruction and elimination identities are kernel checked. -/
theorem commuting_matrices_lowerTriangular (M : Janko4.BinaryMatrix)
    (h : ∀ k : Fin 11, Commute M (Janko4.decodeRows (Coordinates.conjugateRows.get k))) :
    ∀ i j, i < j → M i j = 0 :=
  CommutantProof.lowerTriangular_of_elimination_checks
    CommutantProof.pivots_checked CommutantProof.upper_checked M h

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo

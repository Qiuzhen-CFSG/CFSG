module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.Conjugacy.Data
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.Conjugacy.WordValues.Certificate

/-!+# Assembly of recovered-word evaluation certificates

The straight-line program is proved to agree with Table 1 and §3.4 of
Breuer–Magaard–Wilson (2019) in `WordValues.Program`. Its matrix certificate
checks multiplication and validates inverse nodes by one-sided inverse
equations. This module transfers a checked certificate with the two prescribed
output matrices to the original recovered-word definitions.
-/

public section

namespace BabyMonster.OrderLowerBound

/-- Assemble the two word evaluations from a numerical program certificate.
The output matrices must be the fixed literal data in `Conjugacy.Data`. -/
theorem conjugacy_recovered_values_of_certificate
    (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (v : Fin 242 → AtlasMatrix) (hc : RecoveredWordProgram.Certificate v)
    (hA : v 232 = conjugacyA) (hB : v 241 = conjugacyB) :
    conjugacyA = (↑(recoveredA (matrixGenerators ha hb)) : AtlasMatrix) ∧
    conjugacyB = (↑(recoveredB (matrixGenerators ha hb)) : AtlasMatrix) := by
  obtain ⟨ha', hb'⟩ := hc.outputs ha hb
  rw [hA] at ha'
  rw [hB] at hb'
  simpa only [matrixGenerators, RecoveredWordProgram.recoveredA_eq_node,
    RecoveredWordProgram.recoveredB_eq_node] using And.intro ha' hb'

end BabyMonster.OrderLowerBound

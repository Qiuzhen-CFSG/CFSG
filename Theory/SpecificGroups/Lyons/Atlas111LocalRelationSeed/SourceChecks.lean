module

public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Arithmetic
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationSeed.Data

/-!
# Connecting the packed seed data to the original ATLAS matrices

Repacking base-five rows and the identity is checked by kernel reduction.
The repacking theorem then identifies the decoded matrices with the fixed
units used by `max1Program`. Source: `../Atlas111Source/`.
-/
namespace Lyons.RelationCertificate.Seed

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

private theorem check_a : checkRowsEq a (repackSource atlasARows) = true := by decide +kernel
private theorem check_b : checkRowsEq b (repackSource atlasBRows) = true := by decide +kernel
private theorem check_one : checkRowsEq m0 identityRows = true := by decide +kernel

public theorem a_eq : decode a = ↑atlasA := by
  rw [rows_eq_of_check _ _ check_a, decode_repackSource]
  rfl

public theorem b_eq : decode b = ↑atlasB := by
  rw [rows_eq_of_check _ _ check_b, decode_repackSource]
  rfl

public theorem one_eq : decode m0 = 1 := by
  rw [rows_eq_of_check _ _ check_one, decode_identityRows]

end Lyons.RelationCertificate.Seed

module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.BlockChecking

/-!
# Kernel certificates for Rudvalis orbital rows 512–1023

Each block verifies the two routing circuits and the two row identities
against the ATLAS generators. See `BlockChecking` for the soundness of this
finite enumeration and `Circuit` for the bit-routing interpretation.
-/

namespace Rudvalis.OuterNormalizer.InvarianceCertificate

set_option maxRecDepth 30000 in
private theorem checkedBlock8 : checkBlock facts 8 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock9 : checkBlock facts 9 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock10 : checkBlock facts 10 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock11 : checkBlock facts 11 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock12 : checkBlock facts 12 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock13 : checkBlock facts 13 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock14 : checkBlock facts 14 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock15 : checkBlock facts 15 = true := by decide +kernel

public theorem checkPart1 (b : Fin 8) : checkBlock facts (8 + b.val) = true := by
  rcases b with ⟨b, hb⟩
  have h : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkedBlock8
  · exact checkedBlock9
  · exact checkedBlock10
  · exact checkedBlock11
  · exact checkedBlock12
  · exact checkedBlock13
  · exact checkedBlock14
  · exact checkedBlock15

end Rudvalis.OuterNormalizer.InvarianceCertificate

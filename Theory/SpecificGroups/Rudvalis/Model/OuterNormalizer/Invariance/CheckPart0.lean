module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.BlockChecking

/-!
# Kernel certificates for Rudvalis orbital rows 0–511

Each block verifies the two routing circuits and the two row identities
against the ATLAS generators. See `BlockChecking` for the soundness of this
finite enumeration and `Circuit` for the bit-routing interpretation.
-/

namespace Rudvalis.OuterNormalizer.InvarianceCertificate

set_option maxRecDepth 30000 in
private theorem checkedBlock0 : checkBlock facts 0 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock1 : checkBlock facts 1 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock2 : checkBlock facts 2 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock3 : checkBlock facts 3 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock4 : checkBlock facts 4 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock5 : checkBlock facts 5 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock6 : checkBlock facts 6 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock7 : checkBlock facts 7 = true := by decide +kernel

public theorem checkPart0 (b : Fin 8) : checkBlock facts (0 + b.val) = true := by
  rcases b with ⟨b, hb⟩
  have h : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkedBlock0
  · exact checkedBlock1
  · exact checkedBlock2
  · exact checkedBlock3
  · exact checkedBlock4
  · exact checkedBlock5
  · exact checkedBlock6
  · exact checkedBlock7

end Rudvalis.OuterNormalizer.InvarianceCertificate

module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.BlockChecking

/-!
# Kernel certificates for Rudvalis orbital rows 3584–4059

Each block verifies the two routing circuits and the two row identities
against the ATLAS generators. See `BlockChecking` for the soundness of this
finite enumeration and `Circuit` for the bit-routing interpretation.
-/

namespace Rudvalis.OuterNormalizer.InvarianceCertificate

set_option maxRecDepth 30000 in
private theorem checkedBlock56 : checkBlock facts 56 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock57 : checkBlock facts 57 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock58 : checkBlock facts 58 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock59 : checkBlock facts 59 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock60 : checkBlock facts 60 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock61 : checkBlock facts 61 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock62 : checkBlock facts 62 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock63 : checkBlock facts 63 = true := by decide +kernel

public theorem checkPart7 (b : Fin 8) : checkBlock facts (56 + b.val) = true := by
  rcases b with ⟨b, hb⟩
  have h : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkedBlock56
  · exact checkedBlock57
  · exact checkedBlock58
  · exact checkedBlock59
  · exact checkedBlock60
  · exact checkedBlock61
  · exact checkedBlock62
  · exact checkedBlock63

end Rudvalis.OuterNormalizer.InvarianceCertificate

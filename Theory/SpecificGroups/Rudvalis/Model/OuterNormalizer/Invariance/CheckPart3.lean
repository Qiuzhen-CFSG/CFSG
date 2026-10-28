module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.BlockChecking

/-!
# Kernel certificates for Rudvalis orbital rows 1536–2047

Each block verifies the two routing circuits and the two row identities
against the ATLAS generators. See `BlockChecking` for the soundness of this
finite enumeration and `Circuit` for the bit-routing interpretation.
-/

namespace Rudvalis.OuterNormalizer.InvarianceCertificate

set_option maxRecDepth 30000 in
private theorem checkedBlock24 : checkBlock facts 24 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock25 : checkBlock facts 25 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock26 : checkBlock facts 26 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock27 : checkBlock facts 27 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock28 : checkBlock facts 28 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock29 : checkBlock facts 29 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock30 : checkBlock facts 30 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock31 : checkBlock facts 31 = true := by decide +kernel

public theorem checkPart3 (b : Fin 8) : checkBlock facts (24 + b.val) = true := by
  rcases b with ⟨b, hb⟩
  have h : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkedBlock24
  · exact checkedBlock25
  · exact checkedBlock26
  · exact checkedBlock27
  · exact checkedBlock28
  · exact checkedBlock29
  · exact checkedBlock30
  · exact checkedBlock31

end Rudvalis.OuterNormalizer.InvarianceCertificate

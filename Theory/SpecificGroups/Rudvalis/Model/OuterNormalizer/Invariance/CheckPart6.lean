module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.BlockChecking

/-!
# Kernel certificates for Rudvalis orbital rows 3072–3583

Each block verifies the two routing circuits and the two row identities
against the ATLAS generators. See `BlockChecking` for the soundness of this
finite enumeration and `Circuit` for the bit-routing interpretation.
-/

namespace Rudvalis.OuterNormalizer.InvarianceCertificate

set_option maxRecDepth 30000 in
private theorem checkedBlock48 : checkBlock facts 48 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock49 : checkBlock facts 49 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock50 : checkBlock facts 50 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock51 : checkBlock facts 51 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock52 : checkBlock facts 52 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock53 : checkBlock facts 53 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock54 : checkBlock facts 54 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock55 : checkBlock facts 55 = true := by decide +kernel

public theorem checkPart6 (b : Fin 8) : checkBlock facts (48 + b.val) = true := by
  rcases b with ⟨b, hb⟩
  have h : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkedBlock48
  · exact checkedBlock49
  · exact checkedBlock50
  · exact checkedBlock51
  · exact checkedBlock52
  · exact checkedBlock53
  · exact checkedBlock54
  · exact checkedBlock55

end Rudvalis.OuterNormalizer.InvarianceCertificate

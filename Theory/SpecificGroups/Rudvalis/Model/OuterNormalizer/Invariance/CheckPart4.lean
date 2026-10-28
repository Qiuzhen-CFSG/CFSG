module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.BlockChecking

/-!
# Kernel certificates for Rudvalis orbital rows 2048–2559

Each block verifies the two routing circuits and the two row identities
against the ATLAS generators. See `BlockChecking` for the soundness of this
finite enumeration and `Circuit` for the bit-routing interpretation.
-/

namespace Rudvalis.OuterNormalizer.InvarianceCertificate

set_option maxRecDepth 30000 in
private theorem checkedBlock32 : checkBlock facts 32 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock33 : checkBlock facts 33 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock34 : checkBlock facts 34 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock35 : checkBlock facts 35 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock36 : checkBlock facts 36 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock37 : checkBlock facts 37 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock38 : checkBlock facts 38 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock39 : checkBlock facts 39 = true := by decide +kernel

public theorem checkPart4 (b : Fin 8) : checkBlock facts (32 + b.val) = true := by
  rcases b with ⟨b, hb⟩
  have h : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkedBlock32
  · exact checkedBlock33
  · exact checkedBlock34
  · exact checkedBlock35
  · exact checkedBlock36
  · exact checkedBlock37
  · exact checkedBlock38
  · exact checkedBlock39

end Rudvalis.OuterNormalizer.InvarianceCertificate

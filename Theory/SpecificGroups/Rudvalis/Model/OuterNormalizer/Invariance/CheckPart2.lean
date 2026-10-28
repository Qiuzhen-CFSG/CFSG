module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.BlockChecking

/-!
# Kernel certificates for Rudvalis orbital rows 1024–1535

Each block verifies the two routing circuits and the two row identities
against the ATLAS generators. See `BlockChecking` for the soundness of this
finite enumeration and `Circuit` for the bit-routing interpretation.
-/

namespace Rudvalis.OuterNormalizer.InvarianceCertificate

set_option maxRecDepth 30000 in
private theorem checkedBlock16 : checkBlock facts 16 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock17 : checkBlock facts 17 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock18 : checkBlock facts 18 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock19 : checkBlock facts 19 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock20 : checkBlock facts 20 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock21 : checkBlock facts 21 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock22 : checkBlock facts 22 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock23 : checkBlock facts 23 = true := by decide +kernel

public theorem checkPart2 (b : Fin 8) : checkBlock facts (16 + b.val) = true := by
  rcases b with ⟨b, hb⟩
  have h : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkedBlock16
  · exact checkedBlock17
  · exact checkedBlock18
  · exact checkedBlock19
  · exact checkedBlock20
  · exact checkedBlock21
  · exact checkedBlock22
  · exact checkedBlock23

end Rudvalis.OuterNormalizer.InvarianceCertificate

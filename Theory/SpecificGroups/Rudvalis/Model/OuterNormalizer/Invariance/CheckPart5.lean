module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.BlockChecking

/-!
# Kernel certificates for Rudvalis orbital rows 2560–3071

Each block verifies the two routing circuits and the two row identities
against the ATLAS generators. See `BlockChecking` for the soundness of this
finite enumeration and `Circuit` for the bit-routing interpretation.
-/

namespace Rudvalis.OuterNormalizer.InvarianceCertificate

set_option maxRecDepth 30000 in
private theorem checkedBlock40 : checkBlock facts 40 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock41 : checkBlock facts 41 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock42 : checkBlock facts 42 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock43 : checkBlock facts 43 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock44 : checkBlock facts 44 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock45 : checkBlock facts 45 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock46 : checkBlock facts 46 = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem checkedBlock47 : checkBlock facts 47 = true := by decide +kernel

public theorem checkPart5 (b : Fin 8) : checkBlock facts (40 + b.val) = true := by
  rcases b with ⟨b, hb⟩
  have h : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkedBlock40
  · exact checkedBlock41
  · exact checkedBlock42
  · exact checkedBlock43
  · exact checkedBlock44
  · exact checkedBlock45
  · exact checkedBlock46
  · exact checkedBlock47

end Rudvalis.OuterNormalizer.InvarianceCertificate

module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.CheckPart0
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.CheckPart1
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.CheckPart2
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.CheckPart3
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.CheckPart4
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.CheckPart5
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.CheckPart6
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.CheckPart7

/-!
# The complete Rudvalis orbital computation

Assemble the 64 kernel-checked blocks. For every letter, both circuits route
according to the actual ATLAS generators and transform the corresponding
packed row into the original row. The last block includes all final letters;
its harmless repeated entries result from reduction modulo 4060.
-/

namespace Rudvalis.OuterNormalizer.InvarianceCertificate

private theorem block_checks (b : Fin 64) : checkBlock facts b.val = true := by
  by_cases h0 : b.val < 8
  · have h := checkPart0 ⟨b.val - 0, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 0 ≤ b.val)] using h
  by_cases h1 : b.val < 16
  · have h := checkPart1 ⟨b.val - 8, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 8 ≤ b.val)] using h
  by_cases h2 : b.val < 24
  · have h := checkPart2 ⟨b.val - 16, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 16 ≤ b.val)] using h
  by_cases h3 : b.val < 32
  · have h := checkPart3 ⟨b.val - 24, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 24 ≤ b.val)] using h
  by_cases h4 : b.val < 40
  · have h := checkPart4 ⟨b.val - 32, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 32 ≤ b.val)] using h
  by_cases h5 : b.val < 48
  · have h := checkPart5 ⟨b.val - 40, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 40 ≤ b.val)] using h
  by_cases h6 : b.val < 56
  · have h := checkPart6 ⟨b.val - 48, by omega⟩
    simpa only [Nat.add_sub_of_le (by omega : 48 ≤ b.val)] using h
  have h := checkPart7 ⟨b.val - 56, by have := b.isLt; omega⟩
  simpa only [Nat.add_sub_of_le (by omega : 56 ≤ b.val)] using h

/-- Both routing identities and both packed-row identities, checked for every
letter of the degree-4060 action. -/
public theorem allFacts (x : Fin 4060) : facts x := allFinBlocks facts block_checks x

end Rudvalis.OuterNormalizer.InvarianceCertificate

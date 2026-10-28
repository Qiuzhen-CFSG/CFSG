module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FiniteBound.Criteria

/-!
# Weighted slice bounds for the literal Sylow enumeration

Every commuting slice is contained in its weight-threshold set. The published
table has only six positive nonidentity weights: 2, 8, 16, 32, 64, and 128.
Their threshold sets have respectively 144, 112, 48, 20, 16, and 2 elements.
Each cardinality times its threshold is at most 1024. Thus the threshold
condition alone proves the requested bound, without evaluating any permutation
products or using the independent normal-fixed-mask certificate.

The six counts and the list of possible weights are checked by the kernel
against `WeightData.weight`, on the exact `Enumeration.Index` used by `Slice`.
The data provenance is documented in `FiniteBound/source/README.md` and the
ATLAS-derived stabilizer-chain tables cited by `Enumeration`.
-/

namespace Janko4.LocalStructure.SylowCore.FiniteBoundCertificate

private theorem threshold_card_2 : Fintype.card {j : Index // 2 ≤ weight j} = 144 := by
  decide +kernel

private theorem threshold_card_8 : Fintype.card {j : Index // 8 ≤ weight j} = 112 := by
  decide +kernel

private theorem threshold_card_16 : Fintype.card {j : Index // 16 ≤ weight j} = 48 := by
  decide +kernel

private theorem threshold_card_32 : Fintype.card {j : Index // 32 ≤ weight j} = 20 := by
  decide +kernel

private theorem threshold_card_64 : Fintype.card {j : Index // 64 ≤ weight j} = 16 := by
  decide +kernel

private theorem threshold_card_128 : Fintype.card {j : Index // 128 ≤ weight j} = 2 := by
  decide +kernel

private theorem weight_cases (i : Index) (hi : i ≠ identityIndex) :
    weight i = 0 ∨ weight i = 2 ∨ weight i = 8 ∨ weight i = 16 ∨
      weight i = 32 ∨ weight i = 64 ∨ weight i = 128 := by
  have h : ∀ a b c, (a, b, c) ≠ identityIndex →
      weight (a, b, c) = 0 ∨ weight (a, b, c) = 2 ∨ weight (a, b, c) = 8 ∨
      weight (a, b, c) = 16 ∨ weight (a, b, c) = 32 ∨
      weight (a, b, c) = 64 ∨ weight (a, b, c) = 128 := by decide +kernel
  exact h i.1 i.2.1 i.2.2 hi

private theorem card_slice_le_threshold (i : Index) :
    Nat.card (Slice i) ≤ Fintype.card {j : Index // weight i ≤ weight j} := by
  rw [← Nat.card_eq_fintype_card]
  let f : Slice i → {j : Index // weight i ≤ weight j} :=
    fun j => ⟨j.val, j.property.1⟩
  apply Nat.card_le_card_of_injective f
  intro a b h
  exact Subtype.ext (congrArg (fun j : {j : Index // weight i ≤ weight j} => j.val) h)

/-- The weighted commuting-slice inequality, with no additional premises. -/
public theorem sliceCertificate : SliceCertificate := by
  intro i hi
  refine (Nat.mul_le_mul_right (weight i) (card_slice_le_threshold i)).trans ?_
  rcases weight_cases i hi with h | h | h | h | h | h | h
  · simp only [h, Nat.mul_zero, Nat.zero_le]
  · rw [h, threshold_card_2]
    decide
  · rw [h, threshold_card_8]
    decide
  · rw [h, threshold_card_16]
    decide
  · rw [h, threshold_card_32]
    decide
  · rw [h, threshold_card_64]
  · rw [h, threshold_card_128]
    decide

end Janko4.LocalStructure.SylowCore.FiniteBoundCertificate

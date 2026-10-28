module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.CommutatorTerms.Words

/-!
# Both inclusions for candidate row 1

Explicit products of commutators recover every derived and third-term
generator. Conversely, checked generator bounds and finite relative
normalization extend to the whole generated subgroups via `assemble`.
The concrete third-term generators are also expressed in the derived subgroup.
These are word proofs, independent of the order or full-centralizer claim.

Source: literal candidate row 1 in `SylowNormalEights/source/profile-data.json`;
`source/generate.py` emits the kernel-checked collection certificates.
-/

public section
open scoped commutatorElement
namespace Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.CommutatorTerms

namespace Row1

private theorem derived_lower : maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] ≤
    ⁅maskClosure [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576], maskClosure [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576]⁆ := by
  let K : Subgroup Carrier := ⁅maskClosure [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576], maskClosure [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576]⁆
  have m1105480 : normalForm 1105480 ∈ K := by
    rw [← comm_130_1765409]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1765409 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 130 (by decide +kernel))
  have m165952 : normalForm 165952 ∈ K := by
    rw [← comm_4_1765409]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1765409 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 4 (by decide +kernel))
  have m671744 : normalForm 671744 ∈ K := by
    rw [← comm_1105480_1765409]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1765409 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
  have m32832 : normalForm 32832 ∈ K := by
    rw [← comm_1377808_1765409]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1765409 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1377808 (by decide +kernel))
  have m690240 : normalForm 690240 ∈ K :=
    inverse_mem K 165952 690240 11 m165952 (by decide +kernel)
  have m1181696 : normalForm 1181696 ∈ K := by
    rw [← normalForm_mul_of_collect 690240 32832 1181696 12 (by decide +kernel)]
    exact K.mul_mem m690240 m32832
  have m327680 : normalForm 327680 ∈ K := by
    rw [← comm_64_1765409]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1765409 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 64 (by decide +kernel))
  have m804864 : normalForm 804864 ∈ K := by
    rw [← comm_1765409_1777920]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1765409 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1777920 (by decide +kernel))
  have m1982464 : normalForm 1982464 ∈ K := by
    rw [← normalForm_mul_of_collect 1181696 804864 1982464 7 (by decide +kernel)]
    exact K.mul_mem m1181696 m804864
  have m1310720 : normalForm 1310720 ∈ K := by
    rw [← normalForm_mul_of_collect 671744 1982464 1310720 7 (by decide +kernel)]
    exact K.mul_mem m671744 m1982464
  have m1703936 : normalForm 1703936 ∈ K := by
    rw [← comm_344576_1765409]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1765409 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 344576 (by decide +kernel))
  have m1853440 : normalForm 1853440 ∈ K := by
    rw [← comm_664576_1765409]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1765409 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 664576 (by decide +kernel))
  have m933888 : normalForm 933888 ∈ K := by
    rw [← normalForm_mul_of_collect 1181696 1853440 933888 8 (by decide +kernel)]
    exact K.mul_mem m1181696 m1853440
  have m262144 : normalForm 262144 ∈ K := by
    rw [← normalForm_mul_of_collect 671744 933888 262144 7 (by decide +kernel)]
    exact K.mul_mem m671744 m933888
  have m1048576 : normalForm 1048576 ∈ K := by
    rw [← normalForm_mul_of_collect 1310720 262144 1048576 2 (by decide +kernel)]
    exact K.mul_mem m1310720 m262144
  have m1900544 : normalForm 1900544 ∈ K := by
    rw [← comm_32768_1765409]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1765409 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 32768 (by decide +kernel))
  have m1572864 : normalForm 1572864 ∈ K := by
    rw [← normalForm_mul_of_collect 327680 1900544 1572864 3 (by decide +kernel)]
    exact K.mul_mem m327680 m1900544
  have m1066000 : normalForm 1066000 ∈ K := by
    rw [← comm_4_130]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 130 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 4 (by decide +kernel))
  have m344576 : normalForm 344576 ∈ K := by
    rw [← comm_64_130]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 130 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 64 (by decide +kernel))
  have m1319936 : normalForm 1319936 ∈ K := by
    rw [← comm_130_1777920]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 130 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1777920 (by decide +kernel))
  have m32768 : normalForm 32768 ∈ K := by
    rw [← comm_130_8192]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 130 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 8192 (by decide +kernel))
  have m1377808 : normalForm 1377808 ∈ K := by
    apply product_mem_of_mem K [1066000, 344576, 1572864] 1377808 11
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1066000, m344576, m1572864⟩
    · decide +kernel
  have m16384 : normalForm 16384 ∈ K := by
    apply product_mem_of_mem K [671744, 1703936, 1048576] 16384 4
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m671744, m1703936, m1048576⟩
    · decide +kernel
  have m65536 : normalForm 65536 ∈ K := by
    apply product_mem_of_mem K [327680, 1310720, 1048576] 65536 2
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m327680, m1310720, m1048576⟩
    · decide +kernel
  have m131072 : normalForm 131072 ∈ K := by
    apply product_mem_of_mem K [1703936, 1572864] 131072 3
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1703936, m1572864⟩
    · decide +kernel
  have m524288 : normalForm 524288 ∈ K := by
    apply product_mem_of_mem K [1572864, 1048576] 524288 1
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1572864, m1048576⟩
    · decide +kernel
  apply maskClosure_le
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨m1105480, m1377808, m32832, m344576, m1319936, m804864, m16384, m32768, m65536, m131072, m262144, m524288, m1048576⟩

private theorem third_lower : maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] ≤
    ⁅maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576], maskClosure [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576]⁆ := by
  let K : Subgroup Carrier := ⁅maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576], maskClosure [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576]⁆
  have m671744 : normalForm 671744 ∈ K := by
    rw [← comm_1105480_1765409]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1765409 (by decide +kernel))
  have m835648 : normalForm 835648 ∈ K := by
    rw [← comm_4_1105480]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 4 (by decide +kernel))
  have m2048512 : normalForm 2048512 ∈ K := by
    rw [← comm_1105480_1377808]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1377808 (by decide +kernel))
  have m1966080 : normalForm 1966080 ∈ K := by
    rw [← comm_64_1105480]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 64 (by decide +kernel))
  have m804864 : normalForm 804864 ∈ K := by
    rw [← comm_1105480_1777920]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1777920 (by decide +kernel))
  have m851968 : normalForm 851968 ∈ K := by
    rw [← comm_8192_1105480]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 8192 (by decide +kernel))
  have m262144 : normalForm 262144 ∈ K := by
    rw [← comm_32768_1105480]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 32768 (by decide +kernel))
  have m1048576 : normalForm 1048576 ∈ K := by
    rw [← comm_65536_1105480]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 65536 (by decide +kernel))
  have m32832 : normalForm 32832 ∈ K := by
    rw [← comm_1377808_1765409]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1377808 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1765409 (by decide +kernel))
  have m1359936 : normalForm 1359936 ∈ K :=
    inverse_mem K 835648 1359936 14 m835648 (by decide +kernel)
  have m802816 : normalForm 802816 ∈ K := by
    rw [← normalForm_mul_of_collect 1359936 32832 802816 11 (by decide +kernel)]
    exact K.mul_mem m1359936 m32832
  have m393216 : normalForm 393216 ∈ K := by
    rw [← normalForm_mul_of_collect 671744 802816 393216 5 (by decide +kernel)]
    exact K.mul_mem m671744 m802816
  have m1572864 : normalForm 1572864 ∈ K := by
    rw [← normalForm_mul_of_collect 1966080 393216 1572864 7 (by decide +kernel)]
    exact K.mul_mem m1966080 m393216
  have m163840 : normalForm 163840 ∈ K := by
    rw [← comm_1377808_1777920]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1377808 (by decide +kernel))
      (normalForm_mem [1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1777920 (by decide +kernel))
  have m64 : normalForm 64 ∈ K := by
    apply product_mem_of_mem K [835648, 671744, 163840, 262144] 64 13
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m835648, m671744, m163840, m262144⟩
    · decide +kernel
  have m512 : normalForm 512 ∈ K := by
    apply product_mem_of_mem K [2048512, 671744, 851968, 1572864] 512 21
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m2048512, m671744, m851968, m1572864⟩
    · decide +kernel
  have m2048 : normalForm 2048 ∈ K := by
    apply product_mem_of_mem K [804864, 671744, 1966080, 1572864] 2048 12
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m804864, m671744, m1966080, m1572864⟩
    · decide +kernel
  have m16384 : normalForm 16384 ∈ K := by
    apply product_mem_of_mem K [671744, 1966080, 262144, 1048576] 16384 7
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m671744, m1966080, m262144, m1048576⟩
    · decide +kernel
  have m32768 : normalForm 32768 ∈ K := by
    apply product_mem_of_mem K [163840, 1966080, 262144, 1572864] 32768 7
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m163840, m1966080, m262144, m1572864⟩
    · decide +kernel
  have m65536 : normalForm 65536 ∈ K := by
    apply product_mem_of_mem K [851968, 262144, 1572864, 1048576] 65536 4
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m851968, m262144, m1572864, m1048576⟩
    · decide +kernel
  have m131072 : normalForm 131072 ∈ K := by
    apply product_mem_of_mem K [1966080, 262144, 1572864] 131072 6
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1966080, m262144, m1572864⟩
    · decide +kernel
  have m524288 : normalForm 524288 ∈ K := by
    apply product_mem_of_mem K [1572864, 1048576] 524288 1
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1572864, m1048576⟩
    · decide +kernel
  apply maskClosure_le
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨m64, m512, m2048, m16384, m32768, m65536, m131072, m262144, m524288, m1048576⟩

private theorem third_le_derived : maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] ≤ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] := by
  apply maskClosure_le
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [32832, 32768] 64 1 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [344576, 16384, 65536, 262144] 512 6 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [804864, 16384, 262144, 524288] 2048 6 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [16384] 16384 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [32768] 32768 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536] 65536 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072] 131072 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144] 262144 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [524288] 524288 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1048576] 1048576 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)⟩

private theorem centralizer_pairs : ∀ a ∈ ([1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
    ∀ b ∈ ([1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
      ⁅normalForm a, normalForm b⁆ ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] := by
  have m0 : normalForm 0 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [] 0 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m32768 : normalForm 32768 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [32768] 32768 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m32832 : normalForm 32832 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [32832] 32832 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m131072 : normalForm 131072 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072] 131072 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m163840 : normalForm 163840 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [32768, 131072] 163840 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m165952 : normalForm 165952 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [32832, 804864, 16384, 131072, 262144, 524288, 1048576] 165952 19 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m262144 : normalForm 262144 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144] 262144 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m327680 : normalForm 327680 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 262144] 327680 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m344576 : normalForm 344576 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [344576] 344576 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m524288 : normalForm 524288 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [524288] 524288 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m573440 : normalForm 573440 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [16384, 32768, 524288] 573440 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m671744 : normalForm 671744 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [16384, 131072, 524288] 671744 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m720896 : normalForm 720896 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 131072, 524288] 720896 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m804864 : normalForm 804864 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [804864] 804864 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m835648 : normalForm 835648 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [32832, 16384, 262144, 524288] 835648 1 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m851968 : normalForm 851968 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 262144, 524288] 851968 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m917504 : normalForm 917504 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072, 262144, 524288] 917504 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1048576 : normalForm 1048576 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1048576] 1048576 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1066000 : normalForm 1066000 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1377808, 344576, 524288, 1048576] 1066000 19 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1105480 : normalForm 1105480 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1105480] 1105480 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1245184 : normalForm 1245184 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 131072, 1048576] 1245184 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1310720 : normalForm 1310720 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144, 1048576] 1310720 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1319936 : normalForm 1319936 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1319936] 1319936 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1376256 : normalForm 1376256 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 262144, 1048576] 1376256 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1525760 : normalForm 1525760 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [804864, 65536, 131072, 524288, 1048576] 1525760 5 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1572864 : normalForm 1572864 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [524288, 1048576] 1572864 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1703936 : normalForm 1703936 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072, 524288, 1048576] 1703936 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1835008 : normalForm 1835008 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144, 524288, 1048576] 1835008 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1853440 : normalForm 1853440 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [804864, 1048576] 1853440 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1900544 : normalForm 1900544 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 262144, 524288, 1048576] 1900544 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1917440 : normalForm 1917440 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [344576, 524288, 1048576] 1917440 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1966080 : normalForm 1966080 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072, 262144, 524288, 1048576] 1966080 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m2031616 : normalForm 2031616 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 131072, 262144, 524288, 1048576] 2031616 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m2048512 : normalForm 2048512 ∈ maskClosure [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [344576, 131072, 524288, 1048576] 2048512 1 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by simp, comm_mem_swap _ _ _ (by rw [comm_130_1765409]; exact m1105480), comm_mem_swap _ _ _ (by rw [comm_4_1765409]; exact m165952), comm_mem_swap _ _ _ (by rw [comm_1105480_1765409]; exact m671744), comm_mem_swap _ _ _ (by rw [comm_1377808_1765409]; exact m32832), comm_mem_swap _ _ _ (by rw [comm_64_1765409]; exact m327680), (by rw [comm_1765409_1777920]; exact m804864), comm_mem_swap _ _ _ (by rw [comm_344576_1765409]; exact m1703936), comm_mem_swap _ _ _ (by rw [comm_664576_1765409]; exact m1853440), comm_mem_swap _ _ _ (by rw [comm_1198080_1765409]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_8192_1765409]; exact m2031616), comm_mem_swap _ _ _ (by rw [comm_16384_1765409]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1765409]; exact m1900544), comm_mem_swap _ _ _ (by rw [comm_65536_1765409]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_131072_1765409]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1765409]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_524288_1765409]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1765409]; exact m0)⟩
  · exact ⟨(by rw [comm_130_1765409]; exact m1105480), by simp, comm_mem_swap _ _ _ (by rw [comm_4_130]; exact m1066000), (by rw [comm_130_1105480]; exact m671744), (by rw [comm_130_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_130]; exact m344576), (by rw [comm_130_1777920]; exact m1319936), (by rw [comm_130_344576]; exact m0), (by rw [comm_130_664576]; exact m0), (by rw [comm_130_1198080]; exact m671744), (by rw [comm_130_8192]; exact m32768), (by rw [comm_130_16384]; exact m0), (by rw [comm_130_32768]; exact m0), (by rw [comm_130_65536]; exact m1310720), (by rw [comm_130_131072]; exact m0), (by rw [comm_130_262144]; exact m0), (by rw [comm_130_524288]; exact m0), (by rw [comm_130_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_4_1765409]; exact m165952), (by rw [comm_4_130]; exact m1066000), by simp, (by rw [comm_4_1105480]; exact m835648), (by rw [comm_4_1377808]; exact m1917440), (by rw [comm_4_64]; exact m0), (by rw [comm_4_1777920]; exact m1525760), (by rw [comm_4_344576]; exact m1572864), (by rw [comm_4_664576]; exact m573440), (by rw [comm_4_1198080]; exact m1245184), (by rw [comm_4_8192]; exact m1376256), (by rw [comm_4_16384]; exact m131072), (by rw [comm_4_32768]; exact m1835008), (by rw [comm_4_65536]; exact m0), (by rw [comm_4_131072]; exact m0), (by rw [comm_4_262144]; exact m1572864), (by rw [comm_4_524288]; exact m0), (by rw [comm_4_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_1105480_1765409]; exact m671744), comm_mem_swap _ _ _ (by rw [comm_130_1105480]; exact m671744), comm_mem_swap _ _ _ (by rw [comm_4_1105480]; exact m835648), by simp, (by rw [comm_1105480_1377808]; exact m2048512), comm_mem_swap _ _ _ (by rw [comm_64_1105480]; exact m1966080), (by rw [comm_1105480_1777920]; exact m804864), comm_mem_swap _ _ _ (by rw [comm_344576_1105480]; exact m0), comm_mem_swap _ _ _ (by rw [comm_664576_1105480]; exact m671744), (by rw [comm_1105480_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_1105480]; exact m851968), comm_mem_swap _ _ _ (by rw [comm_16384_1105480]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1105480]; exact m262144), comm_mem_swap _ _ _ (by rw [comm_65536_1105480]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_131072_1105480]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1105480]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1105480]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1105480]; exact m0)⟩
  · exact ⟨(by rw [comm_1377808_1765409]; exact m32832), comm_mem_swap _ _ _ (by rw [comm_130_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_1377808]; exact m1917440), comm_mem_swap _ _ _ (by rw [comm_1105480_1377808]; exact m2048512), by simp, comm_mem_swap _ _ _ (by rw [comm_64_1377808]; exact m1572864), (by rw [comm_1377808_1777920]; exact m163840), comm_mem_swap _ _ _ (by rw [comm_344576_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_664576_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1198080_1377808]; exact m917504), comm_mem_swap _ _ _ (by rw [comm_8192_1377808]; exact m524288), comm_mem_swap _ _ _ (by rw [comm_16384_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1377808]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_131072_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1377808]; exact m0)⟩
  · exact ⟨(by rw [comm_64_1765409]; exact m327680), (by rw [comm_64_130]; exact m344576), comm_mem_swap _ _ _ (by rw [comm_4_64]; exact m0), (by rw [comm_64_1105480]; exact m1966080), (by rw [comm_64_1377808]; exact m1572864), by simp, (by rw [comm_64_1777920]; exact m720896), (by rw [comm_64_344576]; exact m0), (by rw [comm_64_664576]; exact m1966080), (by rw [comm_64_1198080]; exact m0), (by rw [comm_64_8192]; exact m1572864), (by rw [comm_64_16384]; exact m0), (by rw [comm_64_32768]; exact m1572864), (by rw [comm_64_65536]; exact m0), (by rw [comm_64_131072]; exact m0), (by rw [comm_64_262144]; exact m0), (by rw [comm_64_524288]; exact m0), (by rw [comm_64_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_1765409_1777920]; exact m804864), comm_mem_swap _ _ _ (by rw [comm_130_1777920]; exact m1319936), comm_mem_swap _ _ _ (by rw [comm_4_1777920]; exact m1525760), comm_mem_swap _ _ _ (by rw [comm_1105480_1777920]; exact m804864), comm_mem_swap _ _ _ (by rw [comm_1377808_1777920]; exact m163840), comm_mem_swap _ _ _ (by rw [comm_64_1777920]; exact m720896), by simp, comm_mem_swap _ _ _ (by rw [comm_344576_1777920]; exact m1703936), comm_mem_swap _ _ _ (by rw [comm_664576_1777920]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_1198080_1777920]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_8192_1777920]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_1777920]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1777920]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1777920]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_1777920]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1777920]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_524288_1777920]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1777920]; exact m0)⟩
  · exact ⟨(by rw [comm_344576_1765409]; exact m1703936), comm_mem_swap _ _ _ (by rw [comm_130_344576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_344576]; exact m1572864), (by rw [comm_344576_1105480]; exact m0), (by rw [comm_344576_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_344576]; exact m0), (by rw [comm_344576_1777920]; exact m1703936), by simp, (by rw [comm_344576_664576]; exact m0), (by rw [comm_344576_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_344576]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_16384_344576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_344576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_344576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_344576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_344576]; exact m0), (by rw [comm_344576_524288]; exact m0), (by rw [comm_344576_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_664576_1765409]; exact m1853440), comm_mem_swap _ _ _ (by rw [comm_130_664576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_664576]; exact m573440), (by rw [comm_664576_1105480]; exact m671744), (by rw [comm_664576_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_664576]; exact m1966080), (by rw [comm_664576_1777920]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_344576_664576]; exact m0), by simp, (by rw [comm_664576_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_664576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_664576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_664576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_664576]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_131072_664576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_664576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_664576]; exact m0), (by rw [comm_664576_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_1198080_1765409]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_1198080]; exact m671744), comm_mem_swap _ _ _ (by rw [comm_4_1198080]; exact m1245184), comm_mem_swap _ _ _ (by rw [comm_1105480_1198080]; exact m0), (by rw [comm_1198080_1377808]; exact m917504), comm_mem_swap _ _ _ (by rw [comm_64_1198080]; exact m0), (by rw [comm_1198080_1777920]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_344576_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_664576_1198080]; exact m0), by simp, comm_mem_swap _ _ _ (by rw [comm_8192_1198080]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_16384_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1198080]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_65536_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1198080]; exact m0)⟩
  · exact ⟨(by rw [comm_8192_1765409]; exact m2031616), comm_mem_swap _ _ _ (by rw [comm_130_8192]; exact m32768), comm_mem_swap _ _ _ (by rw [comm_4_8192]; exact m1376256), (by rw [comm_8192_1105480]; exact m851968), (by rw [comm_8192_1377808]; exact m524288), comm_mem_swap _ _ _ (by rw [comm_64_8192]; exact m1572864), (by rw [comm_8192_1777920]; exact m0), (by rw [comm_8192_344576]; exact m1572864), (by rw [comm_8192_664576]; exact m0), (by rw [comm_8192_1198080]; exact m1048576), by simp, (by rw [comm_8192_16384]; exact m1048576), (by rw [comm_8192_32768]; exact m0), (by rw [comm_8192_65536]; exact m0), (by rw [comm_8192_131072]; exact m0), (by rw [comm_8192_262144]; exact m0), (by rw [comm_8192_524288]; exact m0), (by rw [comm_8192_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_16384_1765409]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_16384]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_16384]; exact m131072), (by rw [comm_16384_1105480]; exact m0), (by rw [comm_16384_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_16384]; exact m0), (by rw [comm_16384_1777920]; exact m0), (by rw [comm_16384_344576]; exact m0), (by rw [comm_16384_664576]; exact m0), (by rw [comm_16384_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_16384]; exact m1048576), by simp, (by rw [comm_16384_32768]; exact m0), (by rw [comm_16384_65536]; exact m0), (by rw [comm_16384_131072]; exact m0), (by rw [comm_16384_262144]; exact m0), (by rw [comm_16384_524288]; exact m0), (by rw [comm_16384_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_32768_1765409]; exact m1900544), comm_mem_swap _ _ _ (by rw [comm_130_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_32768]; exact m1835008), (by rw [comm_32768_1105480]; exact m262144), (by rw [comm_32768_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_32768]; exact m1572864), (by rw [comm_32768_1777920]; exact m0), (by rw [comm_32768_344576]; exact m0), (by rw [comm_32768_664576]; exact m0), (by rw [comm_32768_1198080]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_8192_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_32768]; exact m0), by simp, (by rw [comm_32768_65536]; exact m0), (by rw [comm_32768_131072]; exact m0), (by rw [comm_32768_262144]; exact m0), (by rw [comm_32768_524288]; exact m0), (by rw [comm_32768_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_65536_1765409]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_65536]; exact m1310720), comm_mem_swap _ _ _ (by rw [comm_4_65536]; exact m0), (by rw [comm_65536_1105480]; exact m1048576), (by rw [comm_65536_1377808]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_64_65536]; exact m0), (by rw [comm_65536_1777920]; exact m0), (by rw [comm_65536_344576]; exact m0), (by rw [comm_65536_664576]; exact m1048576), (by rw [comm_65536_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_65536]; exact m0), by simp, (by rw [comm_65536_131072]; exact m0), (by rw [comm_65536_262144]; exact m0), (by rw [comm_65536_524288]; exact m0), (by rw [comm_65536_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_131072_1765409]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_131072]; exact m0), (by rw [comm_131072_1105480]; exact m0), (by rw [comm_131072_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_131072]; exact m0), (by rw [comm_131072_1777920]; exact m0), (by rw [comm_131072_344576]; exact m0), (by rw [comm_131072_664576]; exact m0), (by rw [comm_131072_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_131072]; exact m0), by simp, (by rw [comm_131072_262144]; exact m0), (by rw [comm_131072_524288]; exact m0), (by rw [comm_131072_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_262144_1765409]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_262144]; exact m1572864), (by rw [comm_262144_1105480]; exact m0), (by rw [comm_262144_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_262144]; exact m0), (by rw [comm_262144_1777920]; exact m1048576), (by rw [comm_262144_344576]; exact m0), (by rw [comm_262144_664576]; exact m0), (by rw [comm_262144_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_262144]; exact m0), by simp, (by rw [comm_262144_524288]; exact m0), (by rw [comm_262144_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_524288_1765409]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_524288]; exact m0), (by rw [comm_524288_1105480]; exact m0), (by rw [comm_524288_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_524288]; exact m0), (by rw [comm_524288_1777920]; exact m0), comm_mem_swap _ _ _ (by rw [comm_344576_524288]; exact m0), (by rw [comm_524288_664576]; exact m0), (by rw [comm_524288_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_524288]; exact m0), by simp, (by rw [comm_524288_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_1048576_1765409]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_1048576]; exact m0), (by rw [comm_1048576_1105480]; exact m0), (by rw [comm_1048576_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_1048576]; exact m0), (by rw [comm_1048576_1777920]; exact m0), comm_mem_swap _ _ _ (by rw [comm_344576_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_664576_1048576]; exact m0), (by rw [comm_1048576_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1048576]; exact m0), by simp⟩

private theorem derived_pairs : ∀ a ∈ ([1105480, 1377808, 32832, 344576, 1319936, 804864, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
    ∀ b ∈ ([1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
      ⁅normalForm a, normalForm b⁆ ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] := by
  have m0 : normalForm 0 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [] 0 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m32832 : normalForm 32832 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [64, 32768] 32832 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m131072 : normalForm 131072 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072] 131072 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m163840 : normalForm 163840 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [32768, 131072] 163840 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m262144 : normalForm 262144 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144] 262144 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m344576 : normalForm 344576 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [512, 16384, 65536, 262144] 344576 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m524288 : normalForm 524288 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [524288] 524288 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m671744 : normalForm 671744 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [16384, 131072, 524288] 671744 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m720896 : normalForm 720896 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 131072, 524288] 720896 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m804864 : normalForm 804864 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [2048, 16384, 262144, 524288] 804864 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m835648 : normalForm 835648 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [64, 16384, 32768, 262144, 524288] 835648 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m851968 : normalForm 851968 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 262144, 524288] 851968 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m917504 : normalForm 917504 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072, 262144, 524288] 917504 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1048576 : normalForm 1048576 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1048576] 1048576 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1097728 : normalForm 1097728 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [16384, 32768, 1048576] 1097728 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1310720 : normalForm 1310720 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144, 1048576] 1310720 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1572864 : normalForm 1572864 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [524288, 1048576] 1572864 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1703936 : normalForm 1703936 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072, 524288, 1048576] 1703936 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1835008 : normalForm 1835008 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144, 524288, 1048576] 1835008 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1900544 : normalForm 1900544 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 262144, 524288, 1048576] 1900544 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1917440 : normalForm 1917440 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [512, 16384, 65536, 262144, 524288, 1048576] 1917440 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1966080 : normalForm 1966080 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072, 262144, 524288, 1048576] 1966080 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m2048512 : normalForm 2048512 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [512, 16384, 65536, 131072, 262144, 524288, 1048576] 2048512 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(by rw [comm_1105480_1765409]; exact m671744), comm_mem_swap _ _ _ (by rw [comm_130_1105480]; exact m671744), comm_mem_swap _ _ _ (by rw [comm_4_1105480]; exact m835648), by simp, (by rw [comm_1105480_1377808]; exact m2048512), comm_mem_swap _ _ _ (by rw [comm_64_1105480]; exact m1966080), (by rw [comm_1105480_1777920]; exact m804864), comm_mem_swap _ _ _ (by rw [comm_344576_1105480]; exact m0), comm_mem_swap _ _ _ (by rw [comm_664576_1105480]; exact m671744), (by rw [comm_1105480_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_1105480]; exact m851968), comm_mem_swap _ _ _ (by rw [comm_16384_1105480]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1105480]; exact m262144), comm_mem_swap _ _ _ (by rw [comm_65536_1105480]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_131072_1105480]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1105480]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1105480]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1105480]; exact m0)⟩
  · exact ⟨(by rw [comm_1377808_1765409]; exact m32832), comm_mem_swap _ _ _ (by rw [comm_130_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_1377808]; exact m1917440), comm_mem_swap _ _ _ (by rw [comm_1105480_1377808]; exact m2048512), by simp, comm_mem_swap _ _ _ (by rw [comm_64_1377808]; exact m1572864), (by rw [comm_1377808_1777920]; exact m163840), comm_mem_swap _ _ _ (by rw [comm_344576_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_664576_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1198080_1377808]; exact m917504), comm_mem_swap _ _ _ (by rw [comm_8192_1377808]; exact m524288), comm_mem_swap _ _ _ (by rw [comm_16384_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1377808]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_131072_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1377808]; exact m0)⟩
  · exact ⟨(by rw [comm_32832_1765409]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_130_32832]; exact m344576), comm_mem_swap _ _ _ (by rw [comm_4_32832]; exact m1835008), (by rw [comm_32832_1105480]; exact m1703936), (by rw [comm_32832_1377808]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_64_32832]; exact m1572864), (by rw [comm_32832_1777920]; exact m720896), (by rw [comm_32832_344576]; exact m0), (by rw [comm_32832_664576]; exact m1966080), (by rw [comm_32832_1198080]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_8192_32832]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_16384_32832]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_32832]; exact m1572864), (by rw [comm_32832_65536]; exact m0), (by rw [comm_32832_131072]; exact m0), (by rw [comm_32832_262144]; exact m0), (by rw [comm_32832_524288]; exact m0), (by rw [comm_32832_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_344576_1765409]; exact m1703936), comm_mem_swap _ _ _ (by rw [comm_130_344576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_344576]; exact m1572864), (by rw [comm_344576_1105480]; exact m0), (by rw [comm_344576_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_344576]; exact m0), (by rw [comm_344576_1777920]; exact m1703936), by simp, (by rw [comm_344576_664576]; exact m0), (by rw [comm_344576_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_344576]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_16384_344576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_344576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_344576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_344576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_344576]; exact m0), (by rw [comm_344576_524288]; exact m0), (by rw [comm_344576_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_1319936_1765409]; exact m804864), comm_mem_swap _ _ _ (by rw [comm_130_1319936]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_1319936]; exact m1097728), comm_mem_swap _ _ _ (by rw [comm_1105480_1319936]; exact m671744), (by rw [comm_1319936_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_1319936]; exact m1966080), (by rw [comm_1319936_1777920]; exact m0), comm_mem_swap _ _ _ (by rw [comm_344576_1319936]; exact m0), comm_mem_swap _ _ _ (by rw [comm_664576_1319936]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1198080_1319936]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_1319936]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_1319936]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1319936]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1319936]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_131072_1319936]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1319936]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1319936]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1319936]; exact m0)⟩
  · exact ⟨(by rw [comm_804864_1765409]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_804864]; exact m671744), comm_mem_swap _ _ _ (by rw [comm_4_804864]; exact m720896), (by rw [comm_804864_1105480]; exact m0), (by rw [comm_804864_1377808]; exact m917504), comm_mem_swap _ _ _ (by rw [comm_64_804864]; exact m0), (by rw [comm_804864_1777920]; exact m0), comm_mem_swap _ _ _ (by rw [comm_344576_804864]; exact m0), comm_mem_swap _ _ _ (by rw [comm_664576_804864]; exact m0), (by rw [comm_804864_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_804864]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_16384_804864]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_804864]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_65536_804864]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_804864]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_804864]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_804864]; exact m0), (by rw [comm_804864_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_16384_1765409]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_16384]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_16384]; exact m131072), (by rw [comm_16384_1105480]; exact m0), (by rw [comm_16384_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_16384]; exact m0), (by rw [comm_16384_1777920]; exact m0), (by rw [comm_16384_344576]; exact m0), (by rw [comm_16384_664576]; exact m0), (by rw [comm_16384_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_16384]; exact m1048576), by simp, (by rw [comm_16384_32768]; exact m0), (by rw [comm_16384_65536]; exact m0), (by rw [comm_16384_131072]; exact m0), (by rw [comm_16384_262144]; exact m0), (by rw [comm_16384_524288]; exact m0), (by rw [comm_16384_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_32768_1765409]; exact m1900544), comm_mem_swap _ _ _ (by rw [comm_130_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_32768]; exact m1835008), (by rw [comm_32768_1105480]; exact m262144), (by rw [comm_32768_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_32768]; exact m1572864), (by rw [comm_32768_1777920]; exact m0), (by rw [comm_32768_344576]; exact m0), (by rw [comm_32768_664576]; exact m0), (by rw [comm_32768_1198080]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_8192_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_32768]; exact m0), by simp, (by rw [comm_32768_65536]; exact m0), (by rw [comm_32768_131072]; exact m0), (by rw [comm_32768_262144]; exact m0), (by rw [comm_32768_524288]; exact m0), (by rw [comm_32768_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_65536_1765409]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_65536]; exact m1310720), comm_mem_swap _ _ _ (by rw [comm_4_65536]; exact m0), (by rw [comm_65536_1105480]; exact m1048576), (by rw [comm_65536_1377808]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_64_65536]; exact m0), (by rw [comm_65536_1777920]; exact m0), (by rw [comm_65536_344576]; exact m0), (by rw [comm_65536_664576]; exact m1048576), (by rw [comm_65536_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_65536]; exact m0), by simp, (by rw [comm_65536_131072]; exact m0), (by rw [comm_65536_262144]; exact m0), (by rw [comm_65536_524288]; exact m0), (by rw [comm_65536_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_131072_1765409]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_131072]; exact m0), (by rw [comm_131072_1105480]; exact m0), (by rw [comm_131072_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_131072]; exact m0), (by rw [comm_131072_1777920]; exact m0), (by rw [comm_131072_344576]; exact m0), (by rw [comm_131072_664576]; exact m0), (by rw [comm_131072_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_131072]; exact m0), by simp, (by rw [comm_131072_262144]; exact m0), (by rw [comm_131072_524288]; exact m0), (by rw [comm_131072_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_262144_1765409]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_262144]; exact m1572864), (by rw [comm_262144_1105480]; exact m0), (by rw [comm_262144_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_262144]; exact m0), (by rw [comm_262144_1777920]; exact m1048576), (by rw [comm_262144_344576]; exact m0), (by rw [comm_262144_664576]; exact m0), (by rw [comm_262144_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_262144]; exact m0), by simp, (by rw [comm_262144_524288]; exact m0), (by rw [comm_262144_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_524288_1765409]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_524288]; exact m0), (by rw [comm_524288_1105480]; exact m0), (by rw [comm_524288_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_524288]; exact m0), (by rw [comm_524288_1777920]; exact m0), comm_mem_swap _ _ _ (by rw [comm_344576_524288]; exact m0), (by rw [comm_524288_664576]; exact m0), (by rw [comm_524288_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_524288]; exact m0), by simp, (by rw [comm_524288_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_1048576_1765409]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_1048576]; exact m0), (by rw [comm_1048576_1105480]; exact m0), (by rw [comm_1048576_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_1048576]; exact m0), (by rw [comm_1048576_1777920]; exact m0), comm_mem_swap _ _ _ (by rw [comm_344576_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_664576_1048576]; exact m0), (by rw [comm_1048576_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1048576]; exact m0), by simp⟩

private theorem third_pairs : ∀ a ∈ ([64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
    ∀ b ∈ ([1765409, 130, 4, 1105480, 1377808, 64, 1777920, 344576, 664576, 1198080, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
      ⁅normalForm a, normalForm b⁆ ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] := by
  have m0 : normalForm 0 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [] 0 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m131072 : normalForm 131072 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072] 131072 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m262144 : normalForm 262144 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144] 262144 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m327680 : normalForm 327680 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 262144] 327680 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m344576 : normalForm 344576 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [512, 16384, 65536, 262144] 344576 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m524288 : normalForm 524288 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [524288] 524288 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m655360 : normalForm 655360 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072, 524288] 655360 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m671744 : normalForm 671744 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [16384, 131072, 524288] 671744 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m720896 : normalForm 720896 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 131072, 524288] 720896 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m917504 : normalForm 917504 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072, 262144, 524288] 917504 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1048576 : normalForm 1048576 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1048576] 1048576 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1114112 : normalForm 1114112 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 1048576] 1114112 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1310720 : normalForm 1310720 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144, 1048576] 1310720 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1572864 : normalForm 1572864 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [524288, 1048576] 1572864 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1703936 : normalForm 1703936 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072, 524288, 1048576] 1703936 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1835008 : normalForm 1835008 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144, 524288, 1048576] 1835008 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1900544 : normalForm 1900544 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 262144, 524288, 1048576] 1900544 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1966080 : normalForm 1966080 ∈ maskClosure [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072, 262144, 524288, 1048576] 1966080 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(by rw [comm_64_1765409]; exact m327680), (by rw [comm_64_130]; exact m344576), comm_mem_swap _ _ _ (by rw [comm_4_64]; exact m0), (by rw [comm_64_1105480]; exact m1966080), (by rw [comm_64_1377808]; exact m1572864), by simp, (by rw [comm_64_1777920]; exact m720896), (by rw [comm_64_344576]; exact m0), (by rw [comm_64_664576]; exact m1966080), (by rw [comm_64_1198080]; exact m0), (by rw [comm_64_8192]; exact m1572864), (by rw [comm_64_16384]; exact m0), (by rw [comm_64_32768]; exact m1572864), (by rw [comm_64_65536]; exact m0), (by rw [comm_64_131072]; exact m0), (by rw [comm_64_262144]; exact m0), (by rw [comm_64_524288]; exact m0), (by rw [comm_64_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_512_1765409]; exact m1703936), comm_mem_swap _ _ _ (by rw [comm_130_512]; exact m1310720), comm_mem_swap _ _ _ (by rw [comm_4_512]; exact m131072), (by rw [comm_512_1105480]; exact m1048576), (by rw [comm_512_1377808]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_64_512]; exact m0), (by rw [comm_512_1777920]; exact m655360), (by rw [comm_512_344576]; exact m0), (by rw [comm_512_664576]; exact m1048576), (by rw [comm_512_1198080]; exact m0), (by rw [comm_512_8192]; exact m524288), (by rw [comm_512_16384]; exact m0), (by rw [comm_512_32768]; exact m0), (by rw [comm_512_65536]; exact m0), (by rw [comm_512_131072]; exact m0), (by rw [comm_512_262144]; exact m0), (by rw [comm_512_524288]; exact m0), (by rw [comm_512_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_2048_1765409]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_2048]; exact m671744), comm_mem_swap _ _ _ (by rw [comm_4_2048]; exact m1114112), (by rw [comm_2048_1105480]; exact m0), (by rw [comm_2048_1377808]; exact m917504), comm_mem_swap _ _ _ (by rw [comm_64_2048]; exact m0), (by rw [comm_2048_1777920]; exact m1048576), (by rw [comm_2048_344576]; exact m0), (by rw [comm_2048_664576]; exact m0), (by rw [comm_2048_1198080]; exact m0), (by rw [comm_2048_8192]; exact m0), (by rw [comm_2048_16384]; exact m0), (by rw [comm_2048_32768]; exact m1048576), (by rw [comm_2048_65536]; exact m0), (by rw [comm_2048_131072]; exact m0), (by rw [comm_2048_262144]; exact m0), (by rw [comm_2048_524288]; exact m0), (by rw [comm_2048_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_16384_1765409]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_16384]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_16384]; exact m131072), (by rw [comm_16384_1105480]; exact m0), (by rw [comm_16384_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_16384]; exact m0), (by rw [comm_16384_1777920]; exact m0), (by rw [comm_16384_344576]; exact m0), (by rw [comm_16384_664576]; exact m0), (by rw [comm_16384_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_16384]; exact m1048576), by simp, (by rw [comm_16384_32768]; exact m0), (by rw [comm_16384_65536]; exact m0), (by rw [comm_16384_131072]; exact m0), (by rw [comm_16384_262144]; exact m0), (by rw [comm_16384_524288]; exact m0), (by rw [comm_16384_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_32768_1765409]; exact m1900544), comm_mem_swap _ _ _ (by rw [comm_130_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_32768]; exact m1835008), (by rw [comm_32768_1105480]; exact m262144), (by rw [comm_32768_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_32768]; exact m1572864), (by rw [comm_32768_1777920]; exact m0), (by rw [comm_32768_344576]; exact m0), (by rw [comm_32768_664576]; exact m0), (by rw [comm_32768_1198080]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_8192_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_32768]; exact m0), by simp, (by rw [comm_32768_65536]; exact m0), (by rw [comm_32768_131072]; exact m0), (by rw [comm_32768_262144]; exact m0), (by rw [comm_32768_524288]; exact m0), (by rw [comm_32768_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_65536_1765409]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_65536]; exact m1310720), comm_mem_swap _ _ _ (by rw [comm_4_65536]; exact m0), (by rw [comm_65536_1105480]; exact m1048576), (by rw [comm_65536_1377808]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_64_65536]; exact m0), (by rw [comm_65536_1777920]; exact m0), (by rw [comm_65536_344576]; exact m0), (by rw [comm_65536_664576]; exact m1048576), (by rw [comm_65536_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_65536]; exact m0), by simp, (by rw [comm_65536_131072]; exact m0), (by rw [comm_65536_262144]; exact m0), (by rw [comm_65536_524288]; exact m0), (by rw [comm_65536_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_131072_1765409]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_131072]; exact m0), (by rw [comm_131072_1105480]; exact m0), (by rw [comm_131072_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_131072]; exact m0), (by rw [comm_131072_1777920]; exact m0), (by rw [comm_131072_344576]; exact m0), (by rw [comm_131072_664576]; exact m0), (by rw [comm_131072_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_131072]; exact m0), by simp, (by rw [comm_131072_262144]; exact m0), (by rw [comm_131072_524288]; exact m0), (by rw [comm_131072_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_262144_1765409]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_262144]; exact m1572864), (by rw [comm_262144_1105480]; exact m0), (by rw [comm_262144_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_262144]; exact m0), (by rw [comm_262144_1777920]; exact m1048576), (by rw [comm_262144_344576]; exact m0), (by rw [comm_262144_664576]; exact m0), (by rw [comm_262144_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_262144]; exact m0), by simp, (by rw [comm_262144_524288]; exact m0), (by rw [comm_262144_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_524288_1765409]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_524288]; exact m0), (by rw [comm_524288_1105480]; exact m0), (by rw [comm_524288_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_524288]; exact m0), (by rw [comm_524288_1777920]; exact m0), comm_mem_swap _ _ _ (by rw [comm_344576_524288]; exact m0), (by rw [comm_524288_664576]; exact m0), (by rw [comm_524288_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_524288]; exact m0), by simp, (by rw [comm_524288_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_1048576_1765409]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4_1048576]; exact m0), (by rw [comm_1048576_1105480]; exact m0), (by rw [comm_1048576_1377808]; exact m0), comm_mem_swap _ _ _ (by rw [comm_64_1048576]; exact m0), (by rw [comm_1048576_1777920]; exact m0), comm_mem_swap _ _ _ (by rw [comm_344576_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_664576_1048576]; exact m0), (by rw [comm_1048576_1198080]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1048576]; exact m0), by simp⟩

/-- Both commutator steps for the literal row 1, including both inclusions. -/
theorem commutator_terms :
    ⁅centralizerCandidate 1, centralizerCandidate 1⁆ = derivedCandidate 1 ∧
      ⁅derivedCandidate 1, centralizerCandidate 1⁆ = thirdCandidate 1 := by
  rw [← thirdMasks_closure]
  exact assemble _ _ _ derived_lower third_lower third_le_derived
    centralizer_pairs derived_pairs third_pairs

end Row1
end Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.CommutatorTerms

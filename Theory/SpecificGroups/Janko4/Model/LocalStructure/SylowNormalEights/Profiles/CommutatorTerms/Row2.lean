module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.CommutatorTerms.Words

/-!
# Both inclusions for candidate row 2

Explicit products of commutators recover every derived and third-term
generator. Conversely, checked generator bounds and finite relative
normalization extend to the whole generated subgroups via `assemble`.
The concrete third-term generators are also expressed in the derived subgroup.
These are word proofs, independent of the order or full-centralizer claim.

Source: literal candidate row 2 in `SylowNormalEights/source/profile-data.json`;
`source/generate.py` emits the kernel-checked collection certificates.
-/

public section
open scoped commutatorElement
namespace Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.CommutatorTerms

namespace Row2

private theorem derived_lower : maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] ≤
    ⁅maskClosure [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576], maskClosure [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576]⁆ := by
  let K : Subgroup Carrier := ⁅maskClosure [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576], maskClosure [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576]⁆
  have m1744456 : normalForm 1744456 ∈ K := by
    rw [← comm_33_130]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 33 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 130 (by decide +kernel))
  have m870976 : normalForm 870976 ∈ K := by
    rw [← comm_33_132]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 33 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 132 (by decide +kernel))
  have m1785856 : normalForm 1785856 ∈ K := by
    rw [← comm_33_1489992]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 33 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1489992 (by decide +kernel))
  have m1638464 : normalForm 1638464 ∈ K := by
    rw [← comm_33_1312272]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 33 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1312272 (by decide +kernel))
  have m1329664 : normalForm 1329664 ∈ K := by
    rw [← normalForm_mul_of_collect 870976 1638464 1329664 11 (by decide +kernel)]
    exact K.mul_mem m870976 m1638464
  have m1048576 : normalForm 1048576 ∈ K := by
    rw [← comm_33_1376320]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 33 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1376320 (by decide +kernel))
  have m1116160 : normalForm 1116160 ∈ K := by
    rw [← comm_33_1634560]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 33 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1634560 (by decide +kernel))
  have m1966080 : normalForm 1966080 ∈ K := by
    rw [← comm_33_344576]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 33 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 344576 (by decide +kernel))
  have m215040 : normalForm 215040 ∈ K := by
    rw [← comm_33_525312]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 33 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 525312 (by decide +kernel))
  have m1196032 : normalForm 1196032 ∈ K := by
    rw [← normalForm_mul_of_collect 1116160 215040 1196032 8 (by decide +kernel)]
    exact K.mul_mem m1116160 m215040
  have m589824 : normalForm 589824 ∈ K := by
    rw [← normalForm_mul_of_collect 1785856 1196032 589824 9 (by decide +kernel)]
    exact K.mul_mem m1785856 m1196032
  have m983040 : normalForm 983040 ∈ K := by
    rw [← comm_33_8192]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 33 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 8192 (by decide +kernel))
  have m393216 : normalForm 393216 ∈ K := by
    rw [← normalForm_mul_of_collect 589824 983040 393216 5 (by decide +kernel)]
    exact K.mul_mem m589824 m983040
  have m1572864 : normalForm 1572864 ∈ K := by
    rw [← normalForm_mul_of_collect 1966080 393216 1572864 7 (by decide +kernel)]
    exact K.mul_mem m1966080 m393216
  have m1900544 : normalForm 1900544 ∈ K := by
    rw [← comm_33_32768]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 33 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 32768 (by decide +kernel))
  have m1310720 : normalForm 1310720 ∈ K := by
    rw [← normalForm_mul_of_collect 589824 1900544 1310720 4 (by decide +kernel)]
    exact K.mul_mem m589824 m1900544
  have m1066000 : normalForm 1066000 ∈ K := by
    rw [← comm_130_132]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 130 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 132 (by decide +kernel))
  have m1753088 : normalForm 1753088 ∈ K := by
    rw [← comm_130_1489992]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 130 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1489992 (by decide +kernel))
  have m98304 : normalForm 98304 ∈ K := by
    rw [← normalForm_mul_of_collect 1785856 1753088 98304 15 (by decide +kernel)]
    exact K.mul_mem m1785856 m1753088
  have m1090560 : normalForm 1090560 ∈ K := by
    rw [← comm_130_1634560]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 130 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1634560 (by decide +kernel))
  have m1105480 : normalForm 1105480 ∈ K := by
    apply product_mem_of_mem K [1744456, 1785856, 589824, 1572864] 1105480 15
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1744456, m1785856, m589824, m1572864⟩
    · decide +kernel
  have m1639952 : normalForm 1639952 ∈ K := by
    apply product_mem_of_mem K [1066000, 1329664, 1116160, 1310720] 1639952 21
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1066000, m1329664, m1116160, m1310720⟩
    · decide +kernel
  have m606720 : normalForm 606720 ∈ K := by
    apply product_mem_of_mem K [1329664, 1116160, 1310720, 1572864] 606720 10
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1329664, m1116160, m1310720, m1572864⟩
    · decide +kernel
  have m67584 : normalForm 67584 ∈ K := by
    apply product_mem_of_mem K [1116160, 1048576] 67584 1
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1116160, m1048576⟩
    · decide +kernel
  have m16384 : normalForm 16384 ∈ K := by
    apply product_mem_of_mem K [1785856, 589824, 1966080, 1310720, 1572864] 16384 16
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1785856, m589824, m1966080, m1310720, m1572864⟩
    · decide +kernel
  have m32768 : normalForm 32768 ∈ K := by
    apply product_mem_of_mem K [98304, 589824, 1572864, 1048576] 32768 3
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m98304, m589824, m1572864, m1048576⟩
    · decide +kernel
  have m65536 : normalForm 65536 ∈ K := by
    apply product_mem_of_mem K [589824, 1572864, 1048576] 65536 2
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m589824, m1572864, m1048576⟩
    · decide +kernel
  have m131072 : normalForm 131072 ∈ K := by
    apply product_mem_of_mem K [1966080, 1310720, 1572864, 1048576] 131072 6
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1966080, m1310720, m1572864, m1048576⟩
    · decide +kernel
  have m262144 : normalForm 262144 ∈ K := by
    apply product_mem_of_mem K [1310720, 1048576] 262144 1
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1310720, m1048576⟩
    · decide +kernel
  have m524288 : normalForm 524288 ∈ K := by
    apply product_mem_of_mem K [1572864, 1048576] 524288 1
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1572864, m1048576⟩
    · decide +kernel
  apply maskClosure_le
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨m1105480, m1639952, m1638464, m606720, m1090560, m67584, m16384, m32768, m65536, m131072, m262144, m524288, m1048576⟩

private theorem third_lower : maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] ≤
    ⁅maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576], maskClosure [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576]⁆ := by
  let K : Subgroup Carrier := ⁅maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576], maskClosure [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576]⁆
  have m671744 : normalForm 671744 ∈ K := by
    rw [← comm_33_1105480]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 33 (by decide +kernel))
  have m81984 : normalForm 81984 ∈ K := by
    rw [← comm_132_1105480]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 132 (by decide +kernel))
  have m851968 : normalForm 851968 ∈ K := by
    rw [← comm_1105480_1489992]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1489992 (by decide +kernel))
  have m999936 : normalForm 999936 ∈ K := by
    rw [← comm_1105480_1312272]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1312272 (by decide +kernel))
  have m917504 : normalForm 917504 ∈ K := by
    rw [← comm_1105480_1376320]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1376320 (by decide +kernel))
  have m83968 : normalForm 83968 ∈ K := by
    rw [← comm_1105480_1634560]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1634560 (by decide +kernel))
  have m1523712 : normalForm 1523712 ∈ K := by
    rw [← comm_525312_1105480]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 525312 (by decide +kernel))
  have m1900544 : normalForm 1900544 ∈ K := by
    rw [← normalForm_mul_of_collect 671744 1523712 1900544 8 (by decide +kernel)]
    exact K.mul_mem m671744 m1523712
  have m1048576 : normalForm 1048576 ∈ K := by
    rw [← normalForm_mul_of_collect 851968 1900544 1048576 6 (by decide +kernel)]
    exact K.mul_mem m851968 m1900544
  have m262144 : normalForm 262144 ∈ K := by
    rw [← comm_32768_1105480]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1105480 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 32768 (by decide +kernel))
  have m1638464 : normalForm 1638464 ∈ K := by
    rw [← comm_33_1639952]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1639952 (by decide +kernel))
      (normalForm_mem [33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 33 (by decide +kernel))
  have m1589248 : normalForm 1589248 ∈ K := by
    rw [← normalForm_mul_of_collect 81984 1638464 1589248 4 (by decide +kernel)]
    exact K.mul_mem m81984 m1638464
  have m1179648 : normalForm 1179648 ∈ K := by
    rw [← normalForm_mul_of_collect 671744 1589248 1179648 4 (by decide +kernel)]
    exact K.mul_mem m671744 m1589248
  have m1835008 : normalForm 1835008 ∈ K := by
    rw [← normalForm_mul_of_collect 917504 1179648 1835008 3 (by decide +kernel)]
    exact K.mul_mem m917504 m1179648
  have m1572864 : normalForm 1572864 ∈ K := by
    rw [← normalForm_mul_of_collect 262144 1835008 1572864 1 (by decide +kernel)]
    exact K.mul_mem m262144 m1835008
  have m64 : normalForm 64 ∈ K := by
    apply product_mem_of_mem K [81984, 671744, 851968, 917504, 1572864, 1048576] 64 12
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m81984, m671744, m851968, m917504, m1572864, m1048576⟩
    · decide +kernel
  have m512 : normalForm 512 ∈ K := by
    apply product_mem_of_mem K [999936, 671744, 851968, 1572864, 1048576] 512 14
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m999936, m671744, m851968, m1572864, m1048576⟩
    · decide +kernel
  have m2048 : normalForm 2048 ∈ K := by
    apply product_mem_of_mem K [83968, 671744, 851968, 917504, 1572864, 1048576] 2048 12
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m83968, m671744, m851968, m917504, m1572864, m1048576⟩
    · decide +kernel
  have m16384 : normalForm 16384 ∈ K := by
    apply product_mem_of_mem K [671744, 917504, 262144] 16384 5
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m671744, m917504, m262144⟩
    · decide +kernel
  have m65536 : normalForm 65536 ∈ K := by
    apply product_mem_of_mem K [851968, 262144, 1572864, 1048576] 65536 4
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m851968, m262144, m1572864, m1048576⟩
    · decide +kernel
  have m131072 : normalForm 131072 ∈ K := by
    apply product_mem_of_mem K [917504, 262144, 1572864, 1048576] 131072 4
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m917504, m262144, m1572864, m1048576⟩
    · decide +kernel
  have m524288 : normalForm 524288 ∈ K := by
    apply product_mem_of_mem K [1572864, 1048576] 524288 1
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1572864, m1048576⟩
    · decide +kernel
  apply maskClosure_le
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨m64, m512, m2048, m16384, m65536, m131072, m262144, m524288, m1048576⟩

private theorem third_le_derived : maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] ≤ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] := by
  apply maskClosure_le
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1638464, 65536, 524288, 1048576] 64 6 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [606720, 16384, 65536, 524288] 512 6 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [67584, 65536] 2048 1 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [16384] 16384 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536] 65536 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072] 131072 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144] 262144 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [524288] 524288 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1048576] 1048576 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)⟩

private theorem centralizer_pairs : ∀ a ∈ ([33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
    ∀ b ∈ ([33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
      ⁅normalForm a, normalForm b⁆ ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] := by
  have m0 : normalForm 0 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [] 0 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m32768 : normalForm 32768 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [32768] 32768 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m215040 : normalForm 215040 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [67584, 16384, 131072] 215040 1 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m262144 : normalForm 262144 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144] 262144 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m393216 : normalForm 393216 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072, 262144] 393216 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m524288 : normalForm 524288 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [524288] 524288 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m606720 : normalForm 606720 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [606720] 606720 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m870976 : normalForm 870976 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1638464, 606720, 67584, 262144, 524288, 1048576] 870976 17 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m983040 : normalForm 983040 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 131072, 262144, 524288] 983040 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1048576 : normalForm 1048576 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1048576] 1048576 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1066000 : normalForm 1066000 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1639952, 606720, 524288, 1048576] 1066000 13 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1090560 : normalForm 1090560 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1090560] 1090560 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1116160 : normalForm 1116160 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [67584, 1048576] 1116160 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1130496 : normalForm 1130496 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [16384, 65536, 1048576] 1130496 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1131008 : normalForm 1131008 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [606720, 524288, 1048576] 1131008 1 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1132544 : normalForm 1132544 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [67584, 16384, 1048576] 1132544 1 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1310720 : normalForm 1310720 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144, 1048576] 1310720 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1376256 : normalForm 1376256 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 262144, 1048576] 1376256 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1441792 : normalForm 1441792 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072, 262144, 1048576] 1441792 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1525760 : normalForm 1525760 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [67584, 16384, 131072, 262144, 1048576] 1525760 1 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1572864 : normalForm 1572864 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [524288, 1048576] 1572864 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1638464 : normalForm 1638464 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1638464] 1638464 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1744456 : normalForm 1744456 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1105480, 16384, 131072, 524288] 1744456 5 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1753088 : normalForm 1753088 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [16384, 32768, 131072, 524288, 1048576] 1753088 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1785856 : normalForm 1785856 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [16384, 65536, 131072, 524288, 1048576] 1785856 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1835008 : normalForm 1835008 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144, 524288, 1048576] 1835008 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1851456 : normalForm 1851456 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1638464, 16384, 65536, 262144] 1851456 8 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1900544 : normalForm 1900544 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 262144, 524288, 1048576] 1900544 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1966080 : normalForm 1966080 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072, 262144, 524288, 1048576] 1966080 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1982464 : normalForm 1982464 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [16384, 131072, 262144, 524288, 1048576] 1982464 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m2048000 : normalForm 2048000 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [16384, 65536, 131072, 262144, 524288, 1048576] 2048000 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m2048512 : normalForm 2048512 ∈ maskClosure [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [606720, 131072, 262144, 1048576] 2048512 2 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by simp, (by rw [comm_33_130]; exact m1744456), (by rw [comm_33_132]; exact m870976), (by rw [comm_33_1489992]; exact m1785856), (by rw [comm_33_1312272]; exact m1638464), (by rw [comm_33_1376320]; exact m1048576), (by rw [comm_33_1634560]; exact m1116160), (by rw [comm_33_344576]; exact m1966080), (by rw [comm_33_525312]; exact m215040), (by rw [comm_33_1263616]; exact m1048576), (by rw [comm_33_8192]; exact m983040), (by rw [comm_33_16384]; exact m1048576), (by rw [comm_33_32768]; exact m1900544), (by rw [comm_33_65536]; exact m1048576), (by rw [comm_33_131072]; exact m1048576), (by rw [comm_33_262144]; exact m1048576), (by rw [comm_33_524288]; exact m0), (by rw [comm_33_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_130]; exact m1744456), by simp, (by rw [comm_130_132]; exact m1066000), (by rw [comm_130_1489992]; exact m1753088), (by rw [comm_130_1312272]; exact m1310720), (by rw [comm_130_1376320]; exact m1131008), (by rw [comm_130_1634560]; exact m1090560), (by rw [comm_130_344576]; exact m0), (by rw [comm_130_525312]; exact m32768), (by rw [comm_130_1263616]; exact m1982464), (by rw [comm_130_8192]; exact m32768), (by rw [comm_130_16384]; exact m0), (by rw [comm_130_32768]; exact m0), (by rw [comm_130_65536]; exact m1310720), (by rw [comm_130_131072]; exact m0), (by rw [comm_130_262144]; exact m0), (by rw [comm_130_524288]; exact m0), (by rw [comm_130_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_132]; exact m870976), comm_mem_swap _ _ _ (by rw [comm_130_132]; exact m1066000), by simp, (by rw [comm_132_1489992]; exact m1851456), (by rw [comm_132_1312272]; exact m606720), (by rw [comm_132_1376320]; exact m0), (by rw [comm_132_1634560]; exact m1132544), (by rw [comm_132_344576]; exact m1572864), (by rw [comm_132_525312]; exact m1130496), (by rw [comm_132_1263616]; exact m1966080), (by rw [comm_132_8192]; exact m1376256), (by rw [comm_132_16384]; exact m1441792), (by rw [comm_132_32768]; exact m1835008), (by rw [comm_132_65536]; exact m0), (by rw [comm_132_131072]; exact m1572864), (by rw [comm_132_262144]; exact m1572864), (by rw [comm_132_524288]; exact m0), (by rw [comm_132_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_1489992]; exact m1785856), comm_mem_swap _ _ _ (by rw [comm_130_1489992]; exact m1753088), comm_mem_swap _ _ _ (by rw [comm_132_1489992]; exact m1851456), by simp, comm_mem_swap _ _ _ (by rw [comm_1312272_1489992]; exact m2048512), comm_mem_swap _ _ _ (by rw [comm_1376320_1489992]; exact m1441792), (by rw [comm_1489992_1634560]; exact m1525760), comm_mem_swap _ _ _ (by rw [comm_344576_1489992]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_525312_1489992]; exact m2048000), comm_mem_swap _ _ _ (by rw [comm_1263616_1489992]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_1489992]; exact m1376256), comm_mem_swap _ _ _ (by rw [comm_16384_1489992]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_32768_1489992]; exact m262144), comm_mem_swap _ _ _ (by rw [comm_65536_1489992]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_131072_1489992]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1489992]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1489992]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1489992]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_1312272]; exact m1638464), comm_mem_swap _ _ _ (by rw [comm_130_1312272]; exact m1310720), comm_mem_swap _ _ _ (by rw [comm_132_1312272]; exact m606720), (by rw [comm_1312272_1489992]; exact m2048512), by simp, (by rw [comm_1312272_1376320]; exact m0), (by rw [comm_1312272_1634560]; exact m393216), comm_mem_swap _ _ _ (by rw [comm_344576_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_525312_1312272]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_1263616_1312272]; exact m1441792), comm_mem_swap _ _ _ (by rw [comm_8192_1312272]; exact m524288), comm_mem_swap _ _ _ (by rw [comm_16384_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1312272]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_131072_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1312272]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_1376320]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_1376320]; exact m1131008), comm_mem_swap _ _ _ (by rw [comm_132_1376320]; exact m0), (by rw [comm_1376320_1489992]; exact m1441792), comm_mem_swap _ _ _ (by rw [comm_1312272_1376320]; exact m0), by simp, (by rw [comm_1376320_1634560]; exact m393216), comm_mem_swap _ _ _ (by rw [comm_344576_1376320]; exact m0), comm_mem_swap _ _ _ (by rw [comm_525312_1376320]; exact m1441792), comm_mem_swap _ _ _ (by rw [comm_1263616_1376320]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_1376320]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_16384_1376320]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1376320]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_65536_1376320]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_1376320]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1376320]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1376320]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1376320]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_1634560]; exact m1116160), comm_mem_swap _ _ _ (by rw [comm_130_1634560]; exact m1090560), comm_mem_swap _ _ _ (by rw [comm_132_1634560]; exact m1132544), comm_mem_swap _ _ _ (by rw [comm_1489992_1634560]; exact m1525760), comm_mem_swap _ _ _ (by rw [comm_1312272_1634560]; exact m393216), comm_mem_swap _ _ _ (by rw [comm_1376320_1634560]; exact m393216), by simp, comm_mem_swap _ _ _ (by rw [comm_344576_1634560]; exact m393216), comm_mem_swap _ _ _ (by rw [comm_525312_1634560]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_1263616_1634560]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_8192_1634560]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_16384_1634560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1634560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1634560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_1634560]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_262144_1634560]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_524288_1634560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1634560]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_344576]; exact m1966080), comm_mem_swap _ _ _ (by rw [comm_130_344576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_344576]; exact m1572864), (by rw [comm_344576_1489992]; exact m1572864), (by rw [comm_344576_1312272]; exact m0), (by rw [comm_344576_1376320]; exact m0), (by rw [comm_344576_1634560]; exact m393216), by simp, (by rw [comm_344576_525312]; exact m1572864), (by rw [comm_344576_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_344576]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_16384_344576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_344576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_344576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_344576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_344576]; exact m0), (by rw [comm_344576_524288]; exact m0), (by rw [comm_344576_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_525312]; exact m215040), comm_mem_swap _ _ _ (by rw [comm_130_525312]; exact m32768), comm_mem_swap _ _ _ (by rw [comm_132_525312]; exact m1130496), (by rw [comm_525312_1489992]; exact m2048000), (by rw [comm_525312_1312272]; exact m1572864), (by rw [comm_525312_1376320]; exact m1441792), (by rw [comm_525312_1634560]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_344576_525312]; exact m1572864), by simp, (by rw [comm_525312_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_525312]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_525312]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_32768_525312]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_525312]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_131072_525312]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_525312]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_525312]; exact m0), (by rw [comm_525312_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_1263616]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_1263616]; exact m1982464), comm_mem_swap _ _ _ (by rw [comm_132_1263616]; exact m1966080), (by rw [comm_1263616_1489992]; exact m0), (by rw [comm_1263616_1312272]; exact m1441792), (by rw [comm_1263616_1376320]; exact m0), (by rw [comm_1263616_1634560]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_344576_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_525312_1263616]; exact m0), by simp, comm_mem_swap _ _ _ (by rw [comm_8192_1263616]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_16384_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1263616]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_65536_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1263616]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_8192]; exact m983040), comm_mem_swap _ _ _ (by rw [comm_130_8192]; exact m32768), comm_mem_swap _ _ _ (by rw [comm_132_8192]; exact m1376256), (by rw [comm_8192_1489992]; exact m1376256), (by rw [comm_8192_1312272]; exact m524288), (by rw [comm_8192_1376320]; exact m1572864), (by rw [comm_8192_1634560]; exact m1048576), (by rw [comm_8192_344576]; exact m1572864), (by rw [comm_8192_525312]; exact m0), (by rw [comm_8192_1263616]; exact m1048576), by simp, (by rw [comm_8192_16384]; exact m1048576), (by rw [comm_8192_32768]; exact m0), (by rw [comm_8192_65536]; exact m0), (by rw [comm_8192_131072]; exact m0), (by rw [comm_8192_262144]; exact m0), (by rw [comm_8192_524288]; exact m0), (by rw [comm_8192_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_16384]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_16384]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_16384]; exact m1441792), (by rw [comm_16384_1489992]; exact m1048576), (by rw [comm_16384_1312272]; exact m0), (by rw [comm_16384_1376320]; exact m0), (by rw [comm_16384_1634560]; exact m0), (by rw [comm_16384_344576]; exact m0), (by rw [comm_16384_525312]; exact m1048576), (by rw [comm_16384_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_16384]; exact m1048576), by simp, (by rw [comm_16384_32768]; exact m0), (by rw [comm_16384_65536]; exact m0), (by rw [comm_16384_131072]; exact m0), (by rw [comm_16384_262144]; exact m0), (by rw [comm_16384_524288]; exact m0), (by rw [comm_16384_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_32768]; exact m1900544), comm_mem_swap _ _ _ (by rw [comm_130_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_32768]; exact m1835008), (by rw [comm_32768_1489992]; exact m262144), (by rw [comm_32768_1312272]; exact m0), (by rw [comm_32768_1376320]; exact m1572864), (by rw [comm_32768_1634560]; exact m0), (by rw [comm_32768_344576]; exact m0), (by rw [comm_32768_525312]; exact m0), (by rw [comm_32768_1263616]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_8192_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_32768]; exact m0), by simp, (by rw [comm_32768_65536]; exact m0), (by rw [comm_32768_131072]; exact m0), (by rw [comm_32768_262144]; exact m0), (by rw [comm_32768_524288]; exact m0), (by rw [comm_32768_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_65536]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_65536]; exact m1310720), comm_mem_swap _ _ _ (by rw [comm_132_65536]; exact m0), (by rw [comm_65536_1489992]; exact m1048576), (by rw [comm_65536_1312272]; exact m1572864), (by rw [comm_65536_1376320]; exact m0), (by rw [comm_65536_1634560]; exact m0), (by rw [comm_65536_344576]; exact m0), (by rw [comm_65536_525312]; exact m1048576), (by rw [comm_65536_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_65536]; exact m0), by simp, (by rw [comm_65536_131072]; exact m0), (by rw [comm_65536_262144]; exact m0), (by rw [comm_65536_524288]; exact m0), (by rw [comm_65536_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_131072]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_131072]; exact m1572864), (by rw [comm_131072_1489992]; exact m0), (by rw [comm_131072_1312272]; exact m0), (by rw [comm_131072_1376320]; exact m0), (by rw [comm_131072_1634560]; exact m1048576), (by rw [comm_131072_344576]; exact m0), (by rw [comm_131072_525312]; exact m0), (by rw [comm_131072_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_131072]; exact m0), by simp, (by rw [comm_131072_262144]; exact m0), (by rw [comm_131072_524288]; exact m0), (by rw [comm_131072_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_262144]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_262144]; exact m1572864), (by rw [comm_262144_1489992]; exact m0), (by rw [comm_262144_1312272]; exact m0), (by rw [comm_262144_1376320]; exact m0), (by rw [comm_262144_1634560]; exact m1048576), (by rw [comm_262144_344576]; exact m0), (by rw [comm_262144_525312]; exact m0), (by rw [comm_262144_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_262144]; exact m0), by simp, (by rw [comm_262144_524288]; exact m0), (by rw [comm_262144_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_524288]; exact m0), (by rw [comm_524288_1489992]; exact m0), (by rw [comm_524288_1312272]; exact m0), (by rw [comm_524288_1376320]; exact m0), (by rw [comm_524288_1634560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_344576_524288]; exact m0), (by rw [comm_524288_525312]; exact m0), (by rw [comm_524288_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_524288]; exact m0), by simp, (by rw [comm_524288_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_1048576]; exact m0), (by rw [comm_1048576_1489992]; exact m0), (by rw [comm_1048576_1312272]; exact m0), (by rw [comm_1048576_1376320]; exact m0), (by rw [comm_1048576_1634560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_344576_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_525312_1048576]; exact m0), (by rw [comm_1048576_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1048576]; exact m0), by simp⟩

private theorem derived_pairs : ∀ a ∈ ([1105480, 1639952, 1638464, 606720, 1090560, 67584, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
    ∀ b ∈ ([33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
      ⁅normalForm a, normalForm b⁆ ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] := by
  have m0 : normalForm 0 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [] 0 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m81984 : normalForm 81984 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [64, 16384, 65536] 81984 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m83968 : normalForm 83968 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [2048, 16384, 65536] 83968 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m262144 : normalForm 262144 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [262144] 262144 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m524288 : normalForm 524288 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [524288] 524288 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m540672 : normalForm 540672 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [16384, 524288] 540672 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m671744 : normalForm 671744 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [16384, 131072, 524288] 671744 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m851968 : normalForm 851968 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [65536, 262144, 524288] 851968 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m917504 : normalForm 917504 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [131072, 262144, 524288] 917504 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m999936 : normalForm 999936 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [512, 16384, 65536, 131072, 262144, 524288] 999936 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1048576 : normalForm 1048576 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [1048576] 1048576 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1131008 : normalForm 1131008 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [512, 16384, 65536, 1048576] 1131008 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1132544 : normalForm 1132544 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [2048, 16384, 65536, 1048576] 1132544 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1310720 : normalForm 1310720 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [262144, 1048576] 1310720 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1441792 : normalForm 1441792 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [131072, 262144, 1048576] 1441792 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1523712 : normalForm 1523712 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [16384, 65536, 131072, 262144, 1048576] 1523712 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1572864 : normalForm 1572864 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [524288, 1048576] 1572864 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1638464 : normalForm 1638464 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [64, 65536, 524288, 1048576] 1638464 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1835008 : normalForm 1835008 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [262144, 524288, 1048576] 1835008 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1900544 : normalForm 1900544 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [65536, 262144, 524288, 1048576] 1900544 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1982464 : normalForm 1982464 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [16384, 131072, 262144, 524288, 1048576] 1982464 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_1105480]; exact m671744), comm_mem_swap _ _ _ (by rw [comm_130_1105480]; exact m671744), comm_mem_swap _ _ _ (by rw [comm_132_1105480]; exact m81984), (by rw [comm_1105480_1489992]; exact m851968), (by rw [comm_1105480_1312272]; exact m999936), (by rw [comm_1105480_1376320]; exact m917504), (by rw [comm_1105480_1634560]; exact m83968), comm_mem_swap _ _ _ (by rw [comm_344576_1105480]; exact m0), comm_mem_swap _ _ _ (by rw [comm_525312_1105480]; exact m1523712), (by rw [comm_1105480_1263616]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_8192_1105480]; exact m851968), comm_mem_swap _ _ _ (by rw [comm_16384_1105480]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1105480]; exact m262144), comm_mem_swap _ _ _ (by rw [comm_65536_1105480]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_131072_1105480]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1105480]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1105480]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1105480]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_1639952]; exact m1638464), comm_mem_swap _ _ _ (by rw [comm_130_1639952]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_1639952]; exact m1131008), comm_mem_swap _ _ _ (by rw [comm_1489992_1639952]; exact m999936), comm_mem_swap _ _ _ (by rw [comm_1312272_1639952]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_1376320_1639952]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1634560_1639952]; exact m1441792), comm_mem_swap _ _ _ (by rw [comm_344576_1639952]; exact m0), comm_mem_swap _ _ _ (by rw [comm_525312_1639952]; exact m524288), comm_mem_swap _ _ _ (by rw [comm_1263616_1639952]; exact m1441792), comm_mem_swap _ _ _ (by rw [comm_8192_1639952]; exact m524288), comm_mem_swap _ _ _ (by rw [comm_16384_1639952]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1639952]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1639952]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_131072_1639952]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1639952]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1639952]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1639952]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_1638464]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_1638464]; exact m1131008), comm_mem_swap _ _ _ (by rw [comm_132_1638464]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_1489992_1638464]; exact m1441792), comm_mem_swap _ _ _ (by rw [comm_1312272_1638464]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1376320_1638464]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1634560_1638464]; exact m1441792), comm_mem_swap _ _ _ (by rw [comm_344576_1638464]; exact m0), comm_mem_swap _ _ _ (by rw [comm_525312_1638464]; exact m1441792), comm_mem_swap _ _ _ (by rw [comm_1263616_1638464]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_1638464]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_16384_1638464]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1638464]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_65536_1638464]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_1638464]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1638464]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1638464]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1638464]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_606720]; exact m917504), comm_mem_swap _ _ _ (by rw [comm_130_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_606720]; exact m0), (by rw [comm_606720_1489992]; exact m1572864), (by rw [comm_606720_1312272]; exact m0), (by rw [comm_606720_1376320]; exact m0), (by rw [comm_606720_1634560]; exact m1441792), comm_mem_swap _ _ _ (by rw [comm_344576_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_525312_606720]; exact m1572864), (by rw [comm_606720_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_606720]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_16384_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_606720]; exact m0), (by rw [comm_606720_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_1090560]; exact m1132544), comm_mem_swap _ _ _ (by rw [comm_130_1090560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_1090560]; exact m540672), (by rw [comm_1090560_1489992]; exact m1982464), (by rw [comm_1090560_1312272]; exact m1048576), (by rw [comm_1090560_1376320]; exact m1441792), (by rw [comm_1090560_1634560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_344576_1090560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_525312_1090560]; exact m0), (by rw [comm_1090560_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_1090560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_1090560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1090560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1090560]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_131072_1090560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1090560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1090560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1090560]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_67584]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_67584]; exact m1982464), comm_mem_swap _ _ _ (by rw [comm_132_67584]; exact m1048576), (by rw [comm_67584_1489992]; exact m1048576), (by rw [comm_67584_1312272]; exact m1441792), (by rw [comm_67584_1376320]; exact m0), (by rw [comm_67584_1634560]; exact m0), (by rw [comm_67584_344576]; exact m0), (by rw [comm_67584_525312]; exact m1048576), (by rw [comm_67584_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_67584]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_67584]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_67584]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_65536_67584]; exact m0), (by rw [comm_67584_131072]; exact m0), (by rw [comm_67584_262144]; exact m0), (by rw [comm_67584_524288]; exact m0), (by rw [comm_67584_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_16384]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_16384]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_16384]; exact m1441792), (by rw [comm_16384_1489992]; exact m1048576), (by rw [comm_16384_1312272]; exact m0), (by rw [comm_16384_1376320]; exact m0), (by rw [comm_16384_1634560]; exact m0), (by rw [comm_16384_344576]; exact m0), (by rw [comm_16384_525312]; exact m1048576), (by rw [comm_16384_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_16384]; exact m1048576), by simp, (by rw [comm_16384_32768]; exact m0), (by rw [comm_16384_65536]; exact m0), (by rw [comm_16384_131072]; exact m0), (by rw [comm_16384_262144]; exact m0), (by rw [comm_16384_524288]; exact m0), (by rw [comm_16384_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_32768]; exact m1900544), comm_mem_swap _ _ _ (by rw [comm_130_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_32768]; exact m1835008), (by rw [comm_32768_1489992]; exact m262144), (by rw [comm_32768_1312272]; exact m0), (by rw [comm_32768_1376320]; exact m1572864), (by rw [comm_32768_1634560]; exact m0), (by rw [comm_32768_344576]; exact m0), (by rw [comm_32768_525312]; exact m0), (by rw [comm_32768_1263616]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_8192_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_32768]; exact m0), by simp, (by rw [comm_32768_65536]; exact m0), (by rw [comm_32768_131072]; exact m0), (by rw [comm_32768_262144]; exact m0), (by rw [comm_32768_524288]; exact m0), (by rw [comm_32768_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_65536]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_65536]; exact m1310720), comm_mem_swap _ _ _ (by rw [comm_132_65536]; exact m0), (by rw [comm_65536_1489992]; exact m1048576), (by rw [comm_65536_1312272]; exact m1572864), (by rw [comm_65536_1376320]; exact m0), (by rw [comm_65536_1634560]; exact m0), (by rw [comm_65536_344576]; exact m0), (by rw [comm_65536_525312]; exact m1048576), (by rw [comm_65536_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_65536]; exact m0), by simp, (by rw [comm_65536_131072]; exact m0), (by rw [comm_65536_262144]; exact m0), (by rw [comm_65536_524288]; exact m0), (by rw [comm_65536_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_131072]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_131072]; exact m1572864), (by rw [comm_131072_1489992]; exact m0), (by rw [comm_131072_1312272]; exact m0), (by rw [comm_131072_1376320]; exact m0), (by rw [comm_131072_1634560]; exact m1048576), (by rw [comm_131072_344576]; exact m0), (by rw [comm_131072_525312]; exact m0), (by rw [comm_131072_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_131072]; exact m0), by simp, (by rw [comm_131072_262144]; exact m0), (by rw [comm_131072_524288]; exact m0), (by rw [comm_131072_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_262144]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_262144]; exact m1572864), (by rw [comm_262144_1489992]; exact m0), (by rw [comm_262144_1312272]; exact m0), (by rw [comm_262144_1376320]; exact m0), (by rw [comm_262144_1634560]; exact m1048576), (by rw [comm_262144_344576]; exact m0), (by rw [comm_262144_525312]; exact m0), (by rw [comm_262144_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_262144]; exact m0), by simp, (by rw [comm_262144_524288]; exact m0), (by rw [comm_262144_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_524288]; exact m0), (by rw [comm_524288_1489992]; exact m0), (by rw [comm_524288_1312272]; exact m0), (by rw [comm_524288_1376320]; exact m0), (by rw [comm_524288_1634560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_344576_524288]; exact m0), (by rw [comm_524288_525312]; exact m0), (by rw [comm_524288_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_524288]; exact m0), by simp, (by rw [comm_524288_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_1048576]; exact m0), (by rw [comm_1048576_1489992]; exact m0), (by rw [comm_1048576_1312272]; exact m0), (by rw [comm_1048576_1376320]; exact m0), (by rw [comm_1048576_1634560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_344576_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_525312_1048576]; exact m0), (by rw [comm_1048576_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1048576]; exact m0), by simp⟩

private theorem third_pairs : ∀ a ∈ ([64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
    ∀ b ∈ ([33, 130, 132, 1489992, 1312272, 1376320, 1634560, 344576, 525312, 1263616, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
      ⁅normalForm a, normalForm b⁆ ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] := by
  have m0 : normalForm 0 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [] 0 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m344576 : normalForm 344576 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [512, 16384, 65536, 262144] 344576 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m393216 : normalForm 393216 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [131072, 262144] 393216 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m524288 : normalForm 524288 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [524288] 524288 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m671744 : normalForm 671744 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [16384, 131072, 524288] 671744 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m917504 : normalForm 917504 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [131072, 262144, 524288] 917504 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1048576 : normalForm 1048576 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [1048576] 1048576 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1310720 : normalForm 1310720 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [262144, 1048576] 1310720 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1441792 : normalForm 1441792 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [131072, 262144, 1048576] 1441792 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1572864 : normalForm 1572864 ∈ maskClosure [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [64, 512, 2048, 16384, 65536, 131072, 262144, 524288, 1048576] [524288, 1048576] 1572864 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_64]; exact m1048576), (by rw [comm_64_130]; exact m344576), (by rw [comm_64_132]; exact m1572864), (by rw [comm_64_1489992]; exact m393216), (by rw [comm_64_1312272]; exact m1572864), (by rw [comm_64_1376320]; exact m0), (by rw [comm_64_1634560]; exact m1441792), (by rw [comm_64_344576]; exact m0), (by rw [comm_64_525312]; exact m393216), (by rw [comm_64_1263616]; exact m0), (by rw [comm_64_8192]; exact m1572864), (by rw [comm_64_16384]; exact m0), (by rw [comm_64_32768]; exact m1572864), (by rw [comm_64_65536]; exact m0), (by rw [comm_64_131072]; exact m0), (by rw [comm_64_262144]; exact m0), (by rw [comm_64_524288]; exact m0), (by rw [comm_64_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_512]; exact m917504), comm_mem_swap _ _ _ (by rw [comm_130_512]; exact m1310720), comm_mem_swap _ _ _ (by rw [comm_132_512]; exact m1441792), (by rw [comm_512_1489992]; exact m1572864), (by rw [comm_512_1312272]; exact m1572864), (by rw [comm_512_1376320]; exact m0), (by rw [comm_512_1634560]; exact m1441792), (by rw [comm_512_344576]; exact m0), (by rw [comm_512_525312]; exact m1572864), (by rw [comm_512_1263616]; exact m0), (by rw [comm_512_8192]; exact m524288), (by rw [comm_512_16384]; exact m0), (by rw [comm_512_32768]; exact m0), (by rw [comm_512_65536]; exact m0), (by rw [comm_512_131072]; exact m0), (by rw [comm_512_262144]; exact m0), (by rw [comm_512_524288]; exact m0), (by rw [comm_512_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_2048]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_2048]; exact m671744), comm_mem_swap _ _ _ (by rw [comm_132_2048]; exact m1048576), (by rw [comm_2048_1489992]; exact m0), (by rw [comm_2048_1312272]; exact m917504), (by rw [comm_2048_1376320]; exact m0), (by rw [comm_2048_1634560]; exact m0), (by rw [comm_2048_344576]; exact m0), (by rw [comm_2048_525312]; exact m0), (by rw [comm_2048_1263616]; exact m0), (by rw [comm_2048_8192]; exact m0), (by rw [comm_2048_16384]; exact m0), (by rw [comm_2048_32768]; exact m1048576), (by rw [comm_2048_65536]; exact m0), (by rw [comm_2048_131072]; exact m0), (by rw [comm_2048_262144]; exact m0), (by rw [comm_2048_524288]; exact m0), (by rw [comm_2048_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_16384]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_16384]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_16384]; exact m1441792), (by rw [comm_16384_1489992]; exact m1048576), (by rw [comm_16384_1312272]; exact m0), (by rw [comm_16384_1376320]; exact m0), (by rw [comm_16384_1634560]; exact m0), (by rw [comm_16384_344576]; exact m0), (by rw [comm_16384_525312]; exact m1048576), (by rw [comm_16384_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_16384]; exact m1048576), by simp, (by rw [comm_16384_32768]; exact m0), (by rw [comm_16384_65536]; exact m0), (by rw [comm_16384_131072]; exact m0), (by rw [comm_16384_262144]; exact m0), (by rw [comm_16384_524288]; exact m0), (by rw [comm_16384_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_65536]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_65536]; exact m1310720), comm_mem_swap _ _ _ (by rw [comm_132_65536]; exact m0), (by rw [comm_65536_1489992]; exact m1048576), (by rw [comm_65536_1312272]; exact m1572864), (by rw [comm_65536_1376320]; exact m0), (by rw [comm_65536_1634560]; exact m0), (by rw [comm_65536_344576]; exact m0), (by rw [comm_65536_525312]; exact m1048576), (by rw [comm_65536_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_65536]; exact m0), by simp, (by rw [comm_65536_131072]; exact m0), (by rw [comm_65536_262144]; exact m0), (by rw [comm_65536_524288]; exact m0), (by rw [comm_65536_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_131072]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_131072]; exact m1572864), (by rw [comm_131072_1489992]; exact m0), (by rw [comm_131072_1312272]; exact m0), (by rw [comm_131072_1376320]; exact m0), (by rw [comm_131072_1634560]; exact m1048576), (by rw [comm_131072_344576]; exact m0), (by rw [comm_131072_525312]; exact m0), (by rw [comm_131072_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_131072]; exact m0), by simp, (by rw [comm_131072_262144]; exact m0), (by rw [comm_131072_524288]; exact m0), (by rw [comm_131072_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_262144]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_130_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_262144]; exact m1572864), (by rw [comm_262144_1489992]; exact m0), (by rw [comm_262144_1312272]; exact m0), (by rw [comm_262144_1376320]; exact m0), (by rw [comm_262144_1634560]; exact m1048576), (by rw [comm_262144_344576]; exact m0), (by rw [comm_262144_525312]; exact m0), (by rw [comm_262144_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_262144]; exact m0), by simp, (by rw [comm_262144_524288]; exact m0), (by rw [comm_262144_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_524288]; exact m0), (by rw [comm_524288_1489992]; exact m0), (by rw [comm_524288_1312272]; exact m0), (by rw [comm_524288_1376320]; exact m0), (by rw [comm_524288_1634560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_344576_524288]; exact m0), (by rw [comm_524288_525312]; exact m0), (by rw [comm_524288_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_524288]; exact m0), by simp, (by rw [comm_524288_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_33_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_130_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_132_1048576]; exact m0), (by rw [comm_1048576_1489992]; exact m0), (by rw [comm_1048576_1312272]; exact m0), (by rw [comm_1048576_1376320]; exact m0), (by rw [comm_1048576_1634560]; exact m0), comm_mem_swap _ _ _ (by rw [comm_344576_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_525312_1048576]; exact m0), (by rw [comm_1048576_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1048576]; exact m0), by simp⟩

/-- Both commutator steps for the literal row 2, including both inclusions. -/
theorem commutator_terms :
    ⁅centralizerCandidate 2, centralizerCandidate 2⁆ = derivedCandidate 2 ∧
      ⁅derivedCandidate 2, centralizerCandidate 2⁆ = thirdCandidate 2 := by
  rw [← thirdMasks_closure]
  exact assemble _ _ _ derived_lower third_lower third_le_derived
    centralizer_pairs derived_pairs third_pairs

end Row2
end Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.CommutatorTerms

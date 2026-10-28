module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.CommutatorTerms.Words

/-!
# Both inclusions for candidate row 0

Explicit products of commutators recover every derived and third-term
generator. Conversely, checked generator bounds and finite relative
normalization extend to the whole generated subgroups via `assemble`.
The concrete third-term generators are also expressed in the derived subgroup.
These are word proofs, independent of the order or full-centralizer claim.

Source: literal candidate row 0 in `SylowNormalEights/source/profile-data.json`;
`source/generate.py` emits the kernel-checked collection certificates.
-/

public section
open scoped commutatorElement
namespace Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.CommutatorTerms

namespace Row0

private theorem derived_lower : maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] ≤
    ⁅maskClosure [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576], maskClosure [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576]⁆ := by
  let K : Subgroup Carrier := ⁅maskClosure [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576], maskClosure [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576]⁆
  have m651336 : normalForm 651336 ∈ K := by
    rw [← comm_2_1179937]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1179937 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 2 (by decide +kernel))
  have m737280 : normalForm 737280 ∈ K := by
    rw [← comm_176200_1179937]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1179937 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 176200 (by decide +kernel))
  have m1998912 : normalForm 1998912 ∈ K := by
    rw [← comm_1179937_1312272]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1179937 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1312272 (by decide +kernel))
  have m1966080 : normalForm 1966080 ∈ K := by
    rw [← comm_32832_1179937]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1179937 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 32832 (by decide +kernel))
  have m1884672 : normalForm 1884672 ∈ K := by
    rw [← comm_128_1179937]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1179937 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 128 (by decide +kernel))
  have m1835008 : normalForm 1835008 ∈ K := by
    rw [← comm_512_1179937]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1179937 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 512 (by decide +kernel))
  have m215040 : normalForm 215040 ∈ K := by
    rw [← comm_1024_1179937]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1179937 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1024 (by decide +kernel))
  have m1048576 : normalForm 1048576 ∈ K := by
    rw [← comm_2048_1179937]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1179937 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 2048 (by decide +kernel))
  have m16384 : normalForm 16384 ∈ K := by
    rw [← comm_4096_1179937]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1179937 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 4096 (by decide +kernel))
  have m720896 : normalForm 720896 ∈ K := by
    rw [← normalForm_mul_of_collect 737280 16384 720896 4 (by decide +kernel)]
    exact K.mul_mem m737280 m16384
  have m983040 : normalForm 983040 ∈ K := by
    rw [← comm_8192_1179937]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1179937 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 8192 (by decide +kernel))
  have m262144 : normalForm 262144 ∈ K := by
    rw [← normalForm_mul_of_collect 720896 983040 262144 7 (by decide +kernel)]
    exact K.mul_mem m720896 m983040
  have m1572864 : normalForm 1572864 ∈ K := by
    rw [← normalForm_mul_of_collect 1835008 262144 1572864 3 (by decide +kernel)]
    exact K.mul_mem m1835008 m262144
  have m1917440 : normalForm 1917440 ∈ K := by
    rw [← comm_2_32832]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 2 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 32832 (by decide +kernel))
  have m98304 : normalForm 98304 ∈ K := by
    rw [← normalForm_mul_of_collect 1884672 1917440 98304 20 (by decide +kernel)]
    exact K.mul_mem m1884672 m1917440
  have m176200 : normalForm 176200 ∈ K := by
    apply product_mem_of_mem K [651336, 737280] 176200 8
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m651336, m737280⟩
    · decide +kernel
  have m32832 : normalForm 32832 ∈ K := by
    apply product_mem_of_mem K [1998912, 1966080] 32832 10
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1998912, m1966080⟩
    · decide +kernel
  have m606720 : normalForm 606720 ∈ K := by
    apply product_mem_of_mem K [1884672, 98304, 1835008, 1572864, 1048576] 606720 14
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1884672, m98304, m1835008, m1572864, m1048576⟩
    · decide +kernel
  have m1263616 : normalForm 1263616 ∈ K := by
    apply product_mem_of_mem K [215040, 1048576] 1263616 0
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m215040, m1048576⟩
    · decide +kernel
  have m32768 : normalForm 32768 ∈ K := by
    apply product_mem_of_mem K [98304, 720896, 1966080, 1835008, 1572864, 1048576] 32768 11
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m98304, m720896, m1966080, m1835008, m1572864, m1048576⟩
    · decide +kernel
  have m65536 : normalForm 65536 ∈ K := by
    apply product_mem_of_mem K [720896, 1966080, 1835008, 1572864, 1048576] 65536 10
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m720896, m1966080, m1835008, m1572864, m1048576⟩
    · decide +kernel
  have m131072 : normalForm 131072 ∈ K := by
    apply product_mem_of_mem K [1966080, 1835008] 131072 6
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1966080, m1835008⟩
    · decide +kernel
  have m524288 : normalForm 524288 ∈ K := by
    apply product_mem_of_mem K [1572864, 1048576] 524288 1
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1572864, m1048576⟩
    · decide +kernel
  apply maskClosure_le
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨m176200, m32832, m606720, m1263616, m16384, m32768, m65536, m131072, m262144, m524288, m1048576⟩

private theorem third_lower : maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] ≤
    ⁅maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576], maskClosure [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576]⁆ := by
  let K : Subgroup Carrier := ⁅maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576], maskClosure [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576]⁆
  have m737280 : normalForm 737280 ∈ K := by
    rw [← comm_176200_1179937]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 176200 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1179937 (by decide +kernel))
  have m606720 : normalForm 606720 ∈ K := by
    rw [← comm_176200_1312272]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 176200 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1312272 (by decide +kernel))
  have m1310720 : normalForm 1310720 ∈ K := by
    rw [← comm_32832_176200]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 176200 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 32832 (by decide +kernel))
  have m1376256 : normalForm 1376256 ∈ K := by
    rw [← comm_4096_176200]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 176200 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 4096 (by decide +kernel))
  have m1966080 : normalForm 1966080 ∈ K := by
    rw [← comm_32832_1179937]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 32832 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1179937 (by decide +kernel))
  have m1572864 : normalForm 1572864 ∈ K := by
    rw [← comm_32832_1312272]
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 32832 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 1312272 (by decide +kernel))
  have m1048576 : normalForm 1048576 ∈ K := by
    rw [← comm_2048_32832]
    apply comm_mem_swap
    exact Subgroup.commutator_mem_commutator
      (normalForm_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 32832 (by decide +kernel))
      (normalForm_mem [1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] 2048 (by decide +kernel))
  have m512 : normalForm 512 ∈ K := by
    apply product_mem_of_mem K [606720, 737280, 1966080, 1310720, 1572864, 1048576] 512 14
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m606720, m737280, m1966080, m1310720, m1572864, m1048576⟩
    · decide +kernel
  have m16384 : normalForm 16384 ∈ K := by
    apply product_mem_of_mem K [737280, 1376256, 1966080] 16384 14
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m737280, m1376256, m1966080⟩
    · decide +kernel
  have m65536 : normalForm 65536 ∈ K := by
    apply product_mem_of_mem K [1376256, 1310720] 65536 3
    · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
      exact ⟨m1376256, m1310720⟩
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
  exact ⟨m512, m16384, m65536, m131072, m262144, m524288, m1048576⟩

private theorem third_le_derived : maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] ≤ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] := by
  apply maskClosure_le
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [606720, 16384, 65536, 524288] 512 6 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [16384] 16384 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536] 65536 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072] 131072 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144] 262144 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [524288] 524288 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel), product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1048576] 1048576 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)⟩

private theorem centralizer_pairs : ∀ a ∈ ([1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
    ∀ b ∈ ([1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
      ⁅normalForm a, normalForm b⁆ ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] := by
  have m0 : normalForm 0 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [] 0 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m16384 : normalForm 16384 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [16384] 16384 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m32768 : normalForm 32768 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [32768] 32768 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m65536 : normalForm 65536 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536] 65536 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m215040 : normalForm 215040 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1263616, 1048576] 215040 1 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m393216 : normalForm 393216 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072, 262144] 393216 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m524288 : normalForm 524288 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [524288] 524288 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m606720 : normalForm 606720 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [606720] 606720 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m651336 : normalForm 651336 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [176200, 16384, 65536, 131072, 524288] 651336 4 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m737280 : normalForm 737280 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [16384, 65536, 131072, 524288] 737280 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m786432 : normalForm 786432 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144, 524288] 786432 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m819200 : normalForm 819200 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [32768, 262144, 524288] 819200 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m917504 : normalForm 917504 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072, 262144, 524288] 917504 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m983040 : normalForm 983040 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 131072, 262144, 524288] 983040 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1048576 : normalForm 1048576 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [1048576] 1048576 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1310720 : normalForm 1310720 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144, 1048576] 1310720 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1376256 : normalForm 1376256 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 262144, 1048576] 1376256 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1572864 : normalForm 1572864 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [524288, 1048576] 1572864 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1835008 : normalForm 1835008 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [262144, 524288, 1048576] 1835008 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1884672 : normalForm 1884672 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [606720, 32768, 65536, 262144, 1048576] 1884672 5 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1900544 : normalForm 1900544 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [65536, 262144, 524288, 1048576] 1900544 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1917440 : normalForm 1917440 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [606720, 262144, 1048576] 1917440 1 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1966080 : normalForm 1966080 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [131072, 262144, 524288, 1048576] 1966080 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1998912 : normalForm 1998912 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [32832, 131072, 262144, 524288, 1048576] 1998912 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m2048000 : normalForm 2048000 ∈ maskClosure [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] [16384, 65536, 131072, 262144, 524288, 1048576] 2048000 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by simp, comm_mem_swap _ _ _ (by rw [comm_2_1179937]; exact m651336), comm_mem_swap _ _ _ (by rw [comm_176200_1179937]; exact m737280), (by rw [comm_1179937_1312272]; exact m1998912), comm_mem_swap _ _ _ (by rw [comm_32832_1179937]; exact m1966080), comm_mem_swap _ _ _ (by rw [comm_128_1179937]; exact m1884672), comm_mem_swap _ _ _ (by rw [comm_512_1179937]; exact m1835008), comm_mem_swap _ _ _ (by rw [comm_1024_1179937]; exact m215040), comm_mem_swap _ _ _ (by rw [comm_2048_1179937]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_4096_1179937]; exact m16384), comm_mem_swap _ _ _ (by rw [comm_8192_1179937]; exact m983040), comm_mem_swap _ _ _ (by rw [comm_16384_1179937]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1179937]; exact m1900544), comm_mem_swap _ _ _ (by rw [comm_65536_1179937]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_131072_1179937]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_262144_1179937]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1179937]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1179937]; exact m0)⟩
  · exact ⟨(by rw [comm_2_1179937]; exact m651336), by simp, (by rw [comm_2_176200]; exact m0), (by rw [comm_2_1312272]; exact m1572864), (by rw [comm_2_32832]; exact m1917440), (by rw [comm_2_128]; exact m0), (by rw [comm_2_512]; exact m1572864), (by rw [comm_2_1024]; exact m0), (by rw [comm_2_2048]; exact m2048000), (by rw [comm_2_4096]; exact m32768), (by rw [comm_2_8192]; exact m32768), (by rw [comm_2_16384]; exact m786432), (by rw [comm_2_32768]; exact m0), (by rw [comm_2_65536]; exact m1310720), (by rw [comm_2_131072]; exact m1572864), (by rw [comm_2_262144]; exact m0), (by rw [comm_2_524288]; exact m0), (by rw [comm_2_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_176200_1179937]; exact m737280), comm_mem_swap _ _ _ (by rw [comm_2_176200]; exact m0), by simp, (by rw [comm_176200_1312272]; exact m606720), comm_mem_swap _ _ _ (by rw [comm_32832_176200]; exact m1310720), comm_mem_swap _ _ _ (by rw [comm_128_176200]; exact m1310720), comm_mem_swap _ _ _ (by rw [comm_512_176200]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_176200]; exact m2048000), comm_mem_swap _ _ _ (by rw [comm_2048_176200]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_176200]; exact m1376256), comm_mem_swap _ _ _ (by rw [comm_8192_176200]; exact m1376256), comm_mem_swap _ _ _ (by rw [comm_16384_176200]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_176200]; exact m1310720), comm_mem_swap _ _ _ (by rw [comm_65536_176200]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_176200]; exact m0), (by rw [comm_176200_262144]; exact m0), (by rw [comm_176200_524288]; exact m0), (by rw [comm_176200_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_1179937_1312272]; exact m1998912), comm_mem_swap _ _ _ (by rw [comm_2_1312272]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_176200_1312272]; exact m606720), by simp, comm_mem_swap _ _ _ (by rw [comm_32832_1312272]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_128_1312272]; exact m786432), comm_mem_swap _ _ _ (by rw [comm_512_1312272]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_1024_1312272]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_2048_1312272]; exact m917504), comm_mem_swap _ _ _ (by rw [comm_4096_1312272]; exact m819200), comm_mem_swap _ _ _ (by rw [comm_8192_1312272]; exact m524288), comm_mem_swap _ _ _ (by rw [comm_16384_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1312272]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_131072_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1312272]; exact m0)⟩
  · exact ⟨(by rw [comm_32832_1179937]; exact m1966080), comm_mem_swap _ _ _ (by rw [comm_2_32832]; exact m1917440), (by rw [comm_32832_176200]; exact m1310720), (by rw [comm_32832_1312272]; exact m1572864), by simp, comm_mem_swap _ _ _ (by rw [comm_128_32832]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_512_32832]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_32832]; exact m393216), comm_mem_swap _ _ _ (by rw [comm_2048_32832]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_4096_32832]; exact m1376256), comm_mem_swap _ _ _ (by rw [comm_8192_32832]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_16384_32832]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_32832]; exact m1572864), (by rw [comm_32832_65536]; exact m0), (by rw [comm_32832_131072]; exact m0), (by rw [comm_32832_262144]; exact m0), (by rw [comm_32832_524288]; exact m0), (by rw [comm_32832_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_128_1179937]; exact m1884672), comm_mem_swap _ _ _ (by rw [comm_2_128]; exact m0), (by rw [comm_128_176200]; exact m1310720), (by rw [comm_128_1312272]; exact m786432), (by rw [comm_128_32832]; exact m1572864), by simp, (by rw [comm_128_512]; exact m786432), (by rw [comm_128_1024]; exact m32768), (by rw [comm_128_2048]; exact m65536), (by rw [comm_128_4096]; exact m0), (by rw [comm_128_8192]; exact m0), (by rw [comm_128_16384]; exact m786432), (by rw [comm_128_32768]; exact m0), (by rw [comm_128_65536]; exact m0), (by rw [comm_128_131072]; exact m1572864), (by rw [comm_128_262144]; exact m0), (by rw [comm_128_524288]; exact m0), (by rw [comm_128_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_512_1179937]; exact m1835008), comm_mem_swap _ _ _ (by rw [comm_2_512]; exact m1572864), (by rw [comm_512_176200]; exact m0), (by rw [comm_512_1312272]; exact m1572864), (by rw [comm_512_32832]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_512]; exact m786432), by simp, (by rw [comm_512_1024]; exact m1572864), (by rw [comm_512_2048]; exact m0), (by rw [comm_512_4096]; exact m786432), (by rw [comm_512_8192]; exact m524288), (by rw [comm_512_16384]; exact m0), (by rw [comm_512_32768]; exact m0), (by rw [comm_512_65536]; exact m0), (by rw [comm_512_131072]; exact m0), (by rw [comm_512_262144]; exact m0), (by rw [comm_512_524288]; exact m0), (by rw [comm_512_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_1024_1179937]; exact m215040), comm_mem_swap _ _ _ (by rw [comm_2_1024]; exact m0), (by rw [comm_1024_176200]; exact m2048000), (by rw [comm_1024_1312272]; exact m1572864), (by rw [comm_1024_32832]; exact m393216), comm_mem_swap _ _ _ (by rw [comm_128_1024]; exact m32768), comm_mem_swap _ _ _ (by rw [comm_512_1024]; exact m1572864), by simp, (by rw [comm_1024_2048]; exact m0), (by rw [comm_1024_4096]; exact m0), (by rw [comm_1024_8192]; exact m0), (by rw [comm_1024_16384]; exact m1048576), (by rw [comm_1024_32768]; exact m0), (by rw [comm_1024_65536]; exact m1048576), (by rw [comm_1024_131072]; exact m0), (by rw [comm_1024_262144]; exact m0), (by rw [comm_1024_524288]; exact m0), (by rw [comm_1024_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_2048_1179937]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_2_2048]; exact m2048000), (by rw [comm_2048_176200]; exact m0), (by rw [comm_2048_1312272]; exact m917504), (by rw [comm_2048_32832]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_128_2048]; exact m65536), comm_mem_swap _ _ _ (by rw [comm_512_2048]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_2048]; exact m0), by simp, (by rw [comm_2048_4096]; exact m0), (by rw [comm_2048_8192]; exact m0), (by rw [comm_2048_16384]; exact m0), (by rw [comm_2048_32768]; exact m1048576), (by rw [comm_2048_65536]; exact m0), (by rw [comm_2048_131072]; exact m0), (by rw [comm_2048_262144]; exact m0), (by rw [comm_2048_524288]; exact m0), (by rw [comm_2048_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_4096_1179937]; exact m16384), comm_mem_swap _ _ _ (by rw [comm_2_4096]; exact m32768), (by rw [comm_4096_176200]; exact m1376256), (by rw [comm_4096_1312272]; exact m819200), (by rw [comm_4096_32832]; exact m1376256), comm_mem_swap _ _ _ (by rw [comm_128_4096]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_4096]; exact m786432), comm_mem_swap _ _ _ (by rw [comm_1024_4096]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_4096]; exact m0), by simp, (by rw [comm_4096_8192]; exact m0), (by rw [comm_4096_16384]; exact m0), (by rw [comm_4096_32768]; exact m0), (by rw [comm_4096_65536]; exact m0), (by rw [comm_4096_131072]; exact m1048576), (by rw [comm_4096_262144]; exact m0), (by rw [comm_4096_524288]; exact m0), (by rw [comm_4096_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_8192_1179937]; exact m983040), comm_mem_swap _ _ _ (by rw [comm_2_8192]; exact m32768), (by rw [comm_8192_176200]; exact m1376256), (by rw [comm_8192_1312272]; exact m524288), (by rw [comm_8192_32832]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_128_8192]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_8192]; exact m524288), comm_mem_swap _ _ _ (by rw [comm_1024_8192]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_8192]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_8192]; exact m0), by simp, (by rw [comm_8192_16384]; exact m1048576), (by rw [comm_8192_32768]; exact m0), (by rw [comm_8192_65536]; exact m0), (by rw [comm_8192_131072]; exact m0), (by rw [comm_8192_262144]; exact m0), (by rw [comm_8192_524288]; exact m0), (by rw [comm_8192_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_16384_1179937]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2_16384]; exact m786432), (by rw [comm_16384_176200]; exact m0), (by rw [comm_16384_1312272]; exact m0), (by rw [comm_16384_32832]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_16384]; exact m786432), comm_mem_swap _ _ _ (by rw [comm_512_16384]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_16384]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_2048_16384]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_16384]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_16384]; exact m1048576), by simp, (by rw [comm_16384_32768]; exact m0), (by rw [comm_16384_65536]; exact m0), (by rw [comm_16384_131072]; exact m0), (by rw [comm_16384_262144]; exact m0), (by rw [comm_16384_524288]; exact m0), (by rw [comm_16384_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_32768_1179937]; exact m1900544), comm_mem_swap _ _ _ (by rw [comm_2_32768]; exact m0), (by rw [comm_32768_176200]; exact m1310720), (by rw [comm_32768_1312272]; exact m0), (by rw [comm_32768_32832]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_128_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_32768]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_4096_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_32768]; exact m0), by simp, (by rw [comm_32768_65536]; exact m0), (by rw [comm_32768_131072]; exact m0), (by rw [comm_32768_262144]; exact m0), (by rw [comm_32768_524288]; exact m0), (by rw [comm_32768_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_65536_1179937]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_2_65536]; exact m1310720), (by rw [comm_65536_176200]; exact m0), (by rw [comm_65536_1312272]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_32832_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_65536]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_2048_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_65536]; exact m0), by simp, (by rw [comm_65536_131072]; exact m0), (by rw [comm_65536_262144]; exact m0), (by rw [comm_65536_524288]; exact m0), (by rw [comm_65536_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_131072_1179937]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_2_131072]; exact m1572864), (by rw [comm_131072_176200]; exact m0), (by rw [comm_131072_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32832_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_131072]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_512_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_131072]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_8192_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_131072]; exact m0), by simp, (by rw [comm_131072_262144]; exact m0), (by rw [comm_131072_524288]; exact m0), (by rw [comm_131072_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_262144_1179937]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_176200_262144]; exact m0), (by rw [comm_262144_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32832_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_262144]; exact m0), by simp, (by rw [comm_262144_524288]; exact m0), (by rw [comm_262144_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_524288_1179937]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_176200_524288]; exact m0), (by rw [comm_524288_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32832_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_524288]; exact m0), by simp, (by rw [comm_524288_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_1048576_1179937]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_176200_1048576]; exact m0), (by rw [comm_1048576_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32832_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1048576]; exact m0), by simp⟩

private theorem derived_pairs : ∀ a ∈ ([176200, 32832, 606720, 1263616, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
    ∀ b ∈ ([1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
      ⁅normalForm a, normalForm b⁆ ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] := by
  have m0 : normalForm 0 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [] 0 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m393216 : normalForm 393216 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [131072, 262144] 393216 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m606720 : normalForm 606720 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [512, 16384, 65536, 524288] 606720 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m737280 : normalForm 737280 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [16384, 65536, 131072, 524288] 737280 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m786432 : normalForm 786432 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [262144, 524288] 786432 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1048576 : normalForm 1048576 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [1048576] 1048576 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1310720 : normalForm 1310720 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [262144, 1048576] 1310720 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1376256 : normalForm 1376256 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [65536, 262144, 1048576] 1376256 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1441792 : normalForm 1441792 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [131072, 262144, 1048576] 1441792 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1572864 : normalForm 1572864 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [524288, 1048576] 1572864 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1900544 : normalForm 1900544 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [65536, 262144, 524288, 1048576] 1900544 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1917440 : normalForm 1917440 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [512, 16384, 65536, 262144, 524288, 1048576] 1917440 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1966080 : normalForm 1966080 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [131072, 262144, 524288, 1048576] 1966080 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m2048000 : normalForm 2048000 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [16384, 65536, 131072, 262144, 524288, 1048576] 2048000 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(by rw [comm_176200_1179937]; exact m737280), comm_mem_swap _ _ _ (by rw [comm_2_176200]; exact m0), by simp, (by rw [comm_176200_1312272]; exact m606720), comm_mem_swap _ _ _ (by rw [comm_32832_176200]; exact m1310720), comm_mem_swap _ _ _ (by rw [comm_128_176200]; exact m1310720), comm_mem_swap _ _ _ (by rw [comm_512_176200]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_176200]; exact m2048000), comm_mem_swap _ _ _ (by rw [comm_2048_176200]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_176200]; exact m1376256), comm_mem_swap _ _ _ (by rw [comm_8192_176200]; exact m1376256), comm_mem_swap _ _ _ (by rw [comm_16384_176200]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_176200]; exact m1310720), comm_mem_swap _ _ _ (by rw [comm_65536_176200]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_176200]; exact m0), (by rw [comm_176200_262144]; exact m0), (by rw [comm_176200_524288]; exact m0), (by rw [comm_176200_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_32832_1179937]; exact m1966080), comm_mem_swap _ _ _ (by rw [comm_2_32832]; exact m1917440), (by rw [comm_32832_176200]; exact m1310720), (by rw [comm_32832_1312272]; exact m1572864), by simp, comm_mem_swap _ _ _ (by rw [comm_128_32832]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_512_32832]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_32832]; exact m393216), comm_mem_swap _ _ _ (by rw [comm_2048_32832]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_4096_32832]; exact m1376256), comm_mem_swap _ _ _ (by rw [comm_8192_32832]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_16384_32832]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_32832]; exact m1572864), (by rw [comm_32832_65536]; exact m0), (by rw [comm_32832_131072]; exact m0), (by rw [comm_32832_262144]; exact m0), (by rw [comm_32832_524288]; exact m0), (by rw [comm_32832_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_606720_1179937]; exact m786432), comm_mem_swap _ _ _ (by rw [comm_2_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_176200_606720]; exact m0), (by rw [comm_606720_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32832_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_606720]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_2048_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_606720]; exact m786432), comm_mem_swap _ _ _ (by rw [comm_8192_606720]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_16384_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_606720]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_606720]; exact m0), (by rw [comm_606720_1048576]; exact m0)⟩
  · exact ⟨comm_mem_swap _ _ _ (by rw [comm_1179937_1263616]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_2_1263616]; exact m2048000), comm_mem_swap _ _ _ (by rw [comm_176200_1263616]; exact m0), (by rw [comm_1263616_1312272]; exact m1441792), comm_mem_swap _ _ _ (by rw [comm_32832_1263616]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_128_1263616]; exact m1376256), comm_mem_swap _ _ _ (by rw [comm_512_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_1263616]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_8192_1263616]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_16384_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1263616]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_65536_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1263616]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1048576_1263616]; exact m0)⟩
  · exact ⟨(by rw [comm_16384_1179937]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2_16384]; exact m786432), (by rw [comm_16384_176200]; exact m0), (by rw [comm_16384_1312272]; exact m0), (by rw [comm_16384_32832]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_16384]; exact m786432), comm_mem_swap _ _ _ (by rw [comm_512_16384]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_16384]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_2048_16384]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_16384]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_16384]; exact m1048576), by simp, (by rw [comm_16384_32768]; exact m0), (by rw [comm_16384_65536]; exact m0), (by rw [comm_16384_131072]; exact m0), (by rw [comm_16384_262144]; exact m0), (by rw [comm_16384_524288]; exact m0), (by rw [comm_16384_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_32768_1179937]; exact m1900544), comm_mem_swap _ _ _ (by rw [comm_2_32768]; exact m0), (by rw [comm_32768_176200]; exact m1310720), (by rw [comm_32768_1312272]; exact m0), (by rw [comm_32768_32832]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_128_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_32768]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_4096_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_32768]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_32768]; exact m0), by simp, (by rw [comm_32768_65536]; exact m0), (by rw [comm_32768_131072]; exact m0), (by rw [comm_32768_262144]; exact m0), (by rw [comm_32768_524288]; exact m0), (by rw [comm_32768_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_65536_1179937]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_2_65536]; exact m1310720), (by rw [comm_65536_176200]; exact m0), (by rw [comm_65536_1312272]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_32832_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_65536]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_2048_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_65536]; exact m0), by simp, (by rw [comm_65536_131072]; exact m0), (by rw [comm_65536_262144]; exact m0), (by rw [comm_65536_524288]; exact m0), (by rw [comm_65536_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_131072_1179937]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_2_131072]; exact m1572864), (by rw [comm_131072_176200]; exact m0), (by rw [comm_131072_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32832_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_131072]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_512_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_131072]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_8192_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_131072]; exact m0), by simp, (by rw [comm_131072_262144]; exact m0), (by rw [comm_131072_524288]; exact m0), (by rw [comm_131072_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_262144_1179937]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_176200_262144]; exact m0), (by rw [comm_262144_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32832_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_262144]; exact m0), by simp, (by rw [comm_262144_524288]; exact m0), (by rw [comm_262144_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_524288_1179937]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_176200_524288]; exact m0), (by rw [comm_524288_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32832_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_524288]; exact m0), by simp, (by rw [comm_524288_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_1048576_1179937]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_176200_1048576]; exact m0), (by rw [comm_1048576_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32832_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1048576]; exact m0), by simp⟩

private theorem third_pairs : ∀ a ∈ ([512, 16384, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
    ∀ b ∈ ([1179937, 2, 176200, 1312272, 32832, 128, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576] : List (Fin (2 ^ 21))),
      ⁅normalForm a, normalForm b⁆ ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] := by
  have m0 : normalForm 0 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [] 0 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m524288 : normalForm 524288 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [524288] 524288 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m786432 : normalForm 786432 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [262144, 524288] 786432 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1048576 : normalForm 1048576 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [1048576] 1048576 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1310720 : normalForm 1310720 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [262144, 1048576] 1310720 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1572864 : normalForm 1572864 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [524288, 1048576] 1572864 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  have m1835008 : normalForm 1835008 ∈ maskClosure [512, 16384, 65536, 131072, 262144, 524288, 1048576] :=
    product_mem [512, 16384, 65536, 131072, 262144, 524288, 1048576] [262144, 524288, 1048576] 1835008 0 (by intro b hb; exact List.Sublist.subset (by decide +kernel) hb) (by decide +kernel)
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(by rw [comm_512_1179937]; exact m1835008), comm_mem_swap _ _ _ (by rw [comm_2_512]; exact m1572864), (by rw [comm_512_176200]; exact m0), (by rw [comm_512_1312272]; exact m1572864), (by rw [comm_512_32832]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_512]; exact m786432), by simp, (by rw [comm_512_1024]; exact m1572864), (by rw [comm_512_2048]; exact m0), (by rw [comm_512_4096]; exact m786432), (by rw [comm_512_8192]; exact m524288), (by rw [comm_512_16384]; exact m0), (by rw [comm_512_32768]; exact m0), (by rw [comm_512_65536]; exact m0), (by rw [comm_512_131072]; exact m0), (by rw [comm_512_262144]; exact m0), (by rw [comm_512_524288]; exact m0), (by rw [comm_512_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_16384_1179937]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2_16384]; exact m786432), (by rw [comm_16384_176200]; exact m0), (by rw [comm_16384_1312272]; exact m0), (by rw [comm_16384_32832]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_16384]; exact m786432), comm_mem_swap _ _ _ (by rw [comm_512_16384]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_16384]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_2048_16384]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_16384]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_16384]; exact m1048576), by simp, (by rw [comm_16384_32768]; exact m0), (by rw [comm_16384_65536]; exact m0), (by rw [comm_16384_131072]; exact m0), (by rw [comm_16384_262144]; exact m0), (by rw [comm_16384_524288]; exact m0), (by rw [comm_16384_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_65536_1179937]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_2_65536]; exact m1310720), (by rw [comm_65536_176200]; exact m0), (by rw [comm_65536_1312272]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_32832_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_65536]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_2048_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_65536]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_65536]; exact m0), by simp, (by rw [comm_65536_131072]; exact m0), (by rw [comm_65536_262144]; exact m0), (by rw [comm_65536_524288]; exact m0), (by rw [comm_65536_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_131072_1179937]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_2_131072]; exact m1572864), (by rw [comm_131072_176200]; exact m0), (by rw [comm_131072_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32832_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_131072]; exact m1572864), comm_mem_swap _ _ _ (by rw [comm_512_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_131072]; exact m1048576), comm_mem_swap _ _ _ (by rw [comm_8192_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_131072]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_131072]; exact m0), by simp, (by rw [comm_131072_262144]; exact m0), (by rw [comm_131072_524288]; exact m0), (by rw [comm_131072_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_262144_1179937]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_176200_262144]; exact m0), (by rw [comm_262144_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32832_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_262144]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_262144]; exact m0), by simp, (by rw [comm_262144_524288]; exact m0), (by rw [comm_262144_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_524288_1179937]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_176200_524288]; exact m0), (by rw [comm_524288_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32832_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_524288]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_524288]; exact m0), by simp, (by rw [comm_524288_1048576]; exact m0)⟩
  · exact ⟨(by rw [comm_1048576_1179937]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_176200_1048576]; exact m0), (by rw [comm_1048576_1312272]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32832_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_128_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_512_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_1024_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_2048_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_4096_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_8192_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_16384_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_32768_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_65536_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_131072_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_262144_1048576]; exact m0), comm_mem_swap _ _ _ (by rw [comm_524288_1048576]; exact m0), by simp⟩

/-- Both commutator steps for the literal row 0, including both inclusions. -/
theorem commutator_terms :
    ⁅centralizerCandidate 0, centralizerCandidate 0⁆ = derivedCandidate 0 ∧
      ⁅derivedCandidate 0, centralizerCandidate 0⁆ = thirdCandidate 0 := by
  rw [← thirdMasks_closure]
  exact assemble _ _ _ derived_lower third_lower third_le_derived
    centralizer_pairs derived_pairs third_pairs

end Row0
end Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.CommutatorTerms

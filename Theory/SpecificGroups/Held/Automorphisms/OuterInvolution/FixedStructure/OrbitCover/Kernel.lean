module
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.OrbitCover.Points
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.OrbitCover.GraphChecks

/-!
# A kernel element is determined by its image of zero

An element of the orbit kernel fixes the 21 certified orbit letters and
preserves the unchanged Held graph. The separating signatures force vertices
1, 2 and 3 once zero is fixed. The existing four-point base then proves
triviality. Five orbit letters also limit the image of zero to the three
images supplied by the central subgroup.

Source: the actual ATLAS Held graph and GLS3 Table 5.3p, outer 2C row.
No order bound for the full fixed subgroup is used.
-/

namespace Held.OuterInvolution.FixedStructure
open Subgroup Held.NormalizerGraph Held.NormalizerGraph.CardBound OrbitCoverCertificate

private theorem kernel_fixes_points (d : candidate) (hd : d ∈ orbitKernel) (i : Fin 21) :
    representation d.val.val (orbitPoints i) = orbitPoints i :=
  (mem_orbitKernel d).mp hd ⟨orbitPoints i, orbitPoints_mem_orbit i⟩

private theorem kernel_preserves_graph (d : candidate) :
    representation d.val.val ∈ preservingGroup :=
  Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup d.val.val.property

public theorem orbitKernel_eq_one_of_fixes_zero (d : candidate) (hd : d ∈ orbitKernel)
    (h0 : representation d.val.val 0 = 0) : d = 1 := by
  have hf := kernel_fixes_points d hd
  have hσ := kernel_preserves_graph d
  have h1 : representation d.val.val 1 = 1 := by
    apply separate1
    apply baseSignature_invariant _ _ hσ
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hf 4
    · exact hf 10
    · exact h0
    · exact hf 17
    · exact hf 0
  have h491 : representation d.val.val 491 = 491 := by
    apply separate491
    apply baseSignature_invariant _ _ hσ
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hf 2
    · exact hf 4
    · exact hf 5
    · exact hf 11
    · exact h0
    · exact hf 6
  have h1185 : representation d.val.val 1185 = 1185 := by
    apply separate1185
    apply baseSignature_invariant _ _ hσ
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hf 1
    · exact hf 4
    · exact hf 9
    · exact hf 13
    · exact h0
    · exact hf 3
  have h1126 : representation d.val.val 1126 = 1126 := by
    apply separate1126
    apply baseSignature_invariant _ _ hσ
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hf 0
    · exact hf 1
    · exact h0
    · exact hf 8
    · exact hf 7
  have h34 : representation d.val.val 34 = 34 := by
    apply separate34
    apply baseSignature_invariant _ _ hσ
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hf 1
    · exact hf 9
    · exact hf 7
    · exact hf 10
    · exact hf 2
  have h2 : representation d.val.val 2 = 2 := by
    apply separate2
    apply baseSignature_invariant _ _ hσ
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hf 16
    · exact h0
    · exact h491
    · exact hf 2
    · exact hf 5
    · exact hf 20
  have h3 : representation d.val.val 3 = 3 := by
    apply separate3
    apply baseSignature_invariant _ _ hσ
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h2
    · exact h1126
    · exact h34
    · exact hf 17
    · exact h1185
    · exact hf 12
  apply Subtype.ext
  apply Subtype.ext
  apply Held.eq_of_four_point_images
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

public theorem orbitKernel_eq_of_zero {d e : candidate} (hd : d ∈ orbitKernel)
    (he : e ∈ orbitKernel)
    (h0 : representation d.val.val 0 = representation e.val.val 0) : d = e := by
  have h : e⁻¹ * d = 1 := by
    apply orbitKernel_eq_one_of_fixes_zero _ (orbitKernel.mul_mem (orbitKernel.inv_mem he) hd)
    change (representation e.val.val).symm (representation d.val.val 0) = 0
    rw [h0]
    exact (representation e.val.val).symm_apply_apply 0
  exact (inv_mul_eq_one.mp h).symm

public theorem orbitKernel_zero_image (d : candidate) (hd : d ∈ orbitKernel) :
    representation d.val.val 0 = 0 ∨ representation d.val.val 0 = 815 ∨
      representation d.val.val 0 = 1356 := by
  apply separate0
  apply baseSignature_invariant _ _ (kernel_preserves_graph d)
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact kernel_fixes_points d hd 2
  · exact kernel_fixes_points d hd 5
  · exact kernel_fixes_points d hd 17
  · exact kernel_fixes_points d hd 9
  · exact kernel_fixes_points d hd 4

public theorem centralGenerator_zero : representation centralGenerator.val.val 0 = 815 := by
  rw [centralGenerator_val, map_pow, map_mul, bray_representation]
  decide +kernel

public theorem centralGenerator_square_zero :
    representation (centralGenerator ^ 2).val.val 0 = 1356 := by
  change representation (centralGenerator.val.val ^ 2) 0 = 1356
  rw [centralGenerator_val, ← pow_mul, map_pow, map_mul, bray_representation]
  decide +kernel

end Held.OuterInvolution.FixedStructure

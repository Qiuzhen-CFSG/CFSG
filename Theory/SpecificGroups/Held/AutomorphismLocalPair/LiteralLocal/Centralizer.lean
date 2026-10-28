module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.LiteralLocal.Action

/-!
# Ambient self-centralization of the literal Held seed

Two word equalities and two graph tests restrict the image of vertex zero to
sixteen possibilities, all realized by central words in the seed. A commuting
graph permutation fixing zero fixes the seed orbit of zero. Graph signatures
then force vertices two, one and three, so the certified four-point base forces
identity. Cancelling the appropriate central word proves the ambient bound.

Every finite check uses the actual ATLAS degree-2058 action and the already
certified representative-generator tables. No order, simplicity, normalizer
recognition, or identification with an intrinsic elementary family is used.
Source: GLS3 Table 5.3p; Aschbacher--Smith, printed p.526.
-/

public section
namespace Held.AutomorphismLocalPair.LiteralLocal
open Subgroup Held.NormalizerGraph

private def test0 (x : Vertex) : Prop :=
  seedPerm 0 x = x ∧ seedPerm 5 x = seedPerm 4 x ∧
    ¬ Adj x (seedPerm 8 x) ∧ Adj x (seedPerm 6 x)
private instance (x : Vertex) : Decidable (test0 x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

private def image0 : Fin 16 → Vertex
  | 0 => 0 | 1 => 1514 | 2 => 355 | 3 => 1044
  | 4 => 581 | 5 => 1796 | 6 => 374 | 7 => 66
  | 8 => 1395 | 9 => 125 | 10 => 919 | 11 => 1112
  | 12 => 1455 | 13 => 1631 | 14 => 219 | _ => 49

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem candidates0 : ∀ x : Vertex, test0 x → ∃ n : Fin 16, image0 n = x := by
  apply TwoLocalCandidates.Cores.allLetters
  decide +kernel

private theorem test0_zero : test0 0 := by decide +kernel

private theorem image_zero (σ : Equiv.Perm Vertex) (hc : CommutesGenerators σ)
    (hg : σ ∈ preservingGroup) : ∃ n : Fin 16, image0 n = σ 0 := by
  apply candidates0
  have h := test0_zero
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hc 0, h.1]
  · rw [← hc 5, ← hc 4, h.2.1]
  · rw [← hc 8]
    exact (hg _ _).not.mpr h.2.2.1
  · rw [← hc 6]
    exact (hg _ _).mpr h.2.2.2

private def separators2 : List Vertex := [0, 384, 581, 919, 374, 417]
private def paths2 : List (List (Fin 12)) :=
  [[], [6, 10, 4], [3], [2, 4], [2, 3], [6, 9]]

private theorem paths2_eq : paths2.map (fun w => walk w 0) = separators2 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem separate2 : ∀ x : Vertex,
    CardBound.baseSignature separators2 x = CardBound.baseSignature separators2 2 → x = 2 := by
  apply TwoLocalCandidates.Cores.allLetters
  decide +kernel

private def separators1 : List Vertex := [0, 553, 55, 1901]
private def paths1 : List (Vertex × List (Fin 12)) :=
  [(0, []), (2, [0, 5]), (0, [4, 7]), (2, [0, 7])]

private theorem paths1_eq : paths1.map (fun rw => walk rw.2 rw.1) = separators1 := by
  decide +kernel

private theorem paths1_roots : ∀ rw ∈ paths1, rw.1 = 0 ∨ rw.1 = 2 := by
  simp [paths1]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem separate1 : ∀ x : Vertex,
    CardBound.baseSignature separators1 x = CardBound.baseSignature separators1 1 → x = 1 := by
  apply TwoLocalCandidates.Cores.allLetters
  decide +kernel

private def separators3 : List Vertex := [2, 123, 18, 36]
private def paths3 : List (Vertex × List (Fin 12)) :=
  [(2, []), (2, [0, 1, 6]), (0, [2, 4, 9]), (2, [1, 2, 4])]

private theorem paths3_eq : paths3.map (fun rw => walk rw.2 rw.1) = separators3 := by
  decide +kernel

private theorem paths3_roots : ∀ rw ∈ paths3, rw.1 = 0 ∨ rw.1 = 2 := by
  simp [paths3]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem separate3 : ∀ x : Vertex,
    CardBound.baseSignature separators3 x = CardBound.baseSignature separators3 3 → x = 3 := by
  apply TwoLocalCandidates.Cores.allLetters
  decide +kernel

private theorem fixes_paths (σ : Equiv.Perm Vertex) (hc : CommutesGenerators σ)
    (h0 : σ 0 = 0) (h2 : σ 2 = 2)
    (paths : List (Vertex × List (Fin 12)))
    (hr : ∀ rw ∈ paths, rw.1 = 0 ∨ rw.1 = 2) :
    ∀ b ∈ paths.map (fun rw => walk rw.2 rw.1), σ b = b := by
  intro b hb
  obtain ⟨⟨r, w⟩, hw, rfl⟩ := List.mem_map.mp hb
  rw [walk_commute σ hc]
  rcases hr (r, w) hw with he | he
  · change r = 0 at he
    rw [he, h0]
  · change r = 2 at he
    rw [he, h2]

/-- A commuting element fixing zero fixes the certified four-point base. -/
theorem centralizer_fix_zero {x : He}
    (hx : x ∈ centralizer (representativeLargeSeed : Set He))
    (h0 : representation x 0 = 0) : x = 1 := by
  let σ := representation x
  have hc := centralizer_commutes hx
  have hg : σ ∈ preservingGroup :=
    Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup x.property
  have hf2 : ∀ b ∈ separators2, σ b = b := by
    intro b hb
    rw [← paths2_eq] at hb
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hb
    rw [walk_commute σ hc, h0]
  have h2 : σ 2 = 2 := separate2 _ (CardBound.baseSignature_invariant _ σ hg hf2 2)
  have hf1 : ∀ b ∈ separators1, σ b = b := by
    rw [← paths1_eq]
    exact fixes_paths σ hc h0 h2 paths1 paths1_roots
  have h1 : σ 1 = 1 := separate1 _ (CardBound.baseSignature_invariant _ σ hg hf1 1)
  have hf3 : ∀ b ∈ separators3, σ b = b := by
    rw [← paths3_eq]
    exact fixes_paths σ hc h0 h2 paths3 paths3_roots
  have h3 : σ 3 = 3 := separate3 _ (CardBound.baseSignature_invariant _ σ hg hf3 3)
  apply eq_of_four_point_images
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

private def centerBasisWord : Fin 4 → List (Fin 12)
  | 0 => [1, 4, 5] | 1 => [2] | 2 => [3] | 3 => [5]

private def centerBasis (i : Fin 4) : He := seedWord (centerBasisWord i)
private def centerPerm (i : Fin 4) : Equiv.Perm Vertex := seedPermWord (centerBasisWord i)

set_option maxRecDepth 16384 in
private theorem basis_commutes_check : ∀ i : Fin 4, ∀ j : Fin 12, ∀ v : Fin 4,
    (seedPerm j * centerPerm i) ⟨v.val, by omega⟩ =
      (centerPerm i * seedPerm j) ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem centerBasis_mem_centralizer (i : Fin 4) :
    centerBasis i ∈ centralizer (representativeLargeSeed : Set He) := by
  apply (mem_centralizer_iff_generators _).mpr
  intro j
  apply eq_of_four_point_images
  simp only [map_mul, centerBasis, ← seedPerm_eq, ← seedPermWord_eq]
  exact basis_commutes_check i j

private def maskIndices (n : Fin 16) : List (Fin 4) :=
  (List.finRange 4).filter (fun i => n.val.testBit i.val)
private def witness (n : Fin 16) : He := ((maskIndices n).map centerBasis).prod
private def witnessPerm (n : Fin 16) : Equiv.Perm Vertex :=
  ((maskIndices n).map centerPerm).prod

private theorem witnessPerm_eq (n : Fin 16) : witnessPerm n = representation (witness n) := by
  simp only [witnessPerm, witness, map_list_prod, List.map_map, Function.comp_def]
  congr 1
  exact List.map_congr_left (fun i _ => seedPermWord_eq (centerBasisWord i))

private theorem witness_mem (n : Fin 16) : witness n ∈ representativeLargeSeed := by
  apply list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact seedWord_mem _

private theorem witness_mem_centralizer (n : Fin 16) :
    witness n ∈ centralizer (representativeLargeSeed : Set He) := by
  apply list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact centerBasis_mem_centralizer i

set_option maxRecDepth 16384 in
private theorem witness_image_check : ∀ n : Fin 16, witnessPerm n 0 = image0 n := by
  decide +kernel

/-- The literal join has no ambient centralizers outside itself. -/
theorem seed_centralizer_le :
    centralizer (representativeLargeSeed : Set He) ≤ representativeLargeSeed := by
  intro x hx
  obtain ⟨n, hn⟩ := image_zero (representation x) (centralizer_commutes hx)
    (Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup x.property)
  have him : representation (witness n) 0 = representation x 0 := by
    rw [← witnessPerm_eq, witness_image_check, hn]
  have hc : (witness n)⁻¹ * x ∈ centralizer (representativeLargeSeed : Set He) :=
    mul_mem (inv_mem (witness_mem_centralizer n)) hx
  have hid : (witness n)⁻¹ * x = 1 := centralizer_fix_zero hc (by
    change (representation (witness n)).symm (representation x 0) = 0
    rw [← him]
    exact Equiv.symm_apply_apply _ _)
  rw [← inv_mul_eq_one.mp hid]
  exact witness_mem n

end Held.AutomorphismLocalPair.LiteralLocal

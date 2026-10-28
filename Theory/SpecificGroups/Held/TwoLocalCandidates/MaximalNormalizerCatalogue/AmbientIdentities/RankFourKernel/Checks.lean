module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.RankFourKernel.Data

/-!
# Finite certificates for the two Held short-orbit kernels

The four generators commute and square to one; binary collection therefore
covers the actual subgroup with sixteen products. Kernel-checked evaluations
show that a two-point orbit is fixed by the fourth generator, the common
involution. Three selected two-point orbits separate the other fourteen
nonidentity products. All computations use previously certified permutation
tables; the retained discovery script selects witnesses but is not trusted.

Source: ATLAS HeG1-p2058B0, the catalogue word data, and GLS3 Table 5.3p.
-/

public section
namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankFourKernel
open Subgroup
open Theory.GroupTheory.BinaryCollection

set_option maxRecDepth 8192 in
private theorem squares_check : ∀ k : Fin 2, ∀ i : Fin 4, ∀ x : Fin 4,
    (perm k i * perm k i) ⟨x.val, by omega⟩ = ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem commute_check : ∀ k : Fin 2, ∀ i j : Fin 4, ∀ x : Fin 4,
    (perm k i * perm k j) ⟨x.val, by omega⟩ =
      (perm k j * perm k i) ⟨x.val, by omega⟩ := by
  decide +kernel

theorem gen_square (k : Fin 2) (i : Fin 4) : gen k i * gen k i = 1 := by
  apply eq_of_four_point_images
  simp only [map_mul, map_one, ← perm_eq]
  exact squares_check k i

theorem gen_commute (k : Fin 2) (i j : Fin 4) : gen k i * gen k j = gen k j * gen k i := by
  apply eq_of_four_point_images
  simp only [map_mul, ← perm_eq]
  exact commute_check k i j

private theorem triangular_of_commuting {G : Type*} [Group G] (l : List G)
    (hs : ∀ a ∈ l, a * a = 1) (hc : ∀ a ∈ l, ∀ b ∈ l, a * b = b * a) :
    triangular l := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    refine ⟨?_, ?_, ih (fun b hb => hs b (List.mem_cons_of_mem _ hb))
      (fun b hb c hc' => hc b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc'))⟩
    · rw [hs a (List.mem_cons_self)]
      exact one_mem _
    · intro b hb
      have he : a⁻¹ * b * a = b := by
        rw [mul_assoc, ← hc a List.mem_cons_self b (List.mem_cons_of_mem _ hb),
          inv_mul_cancel_left]
      rw [he]
      exact subset_closure hb

theorem normalForm_cover (k : Fin 2) {x : He} (hx : x ∈ ambient (row k)) :
    ∃ n : Fin 16, normalForm k n = x := by
  rw [ambient_eq_closure] at hx
  have ht : triangular (List.ofFn (gen k)) := by
    apply triangular_of_commuting
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact gen_square k i
    · intro a ha b hb
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
      exact gen_commute k i j
  obtain ⟨n, hn, he⟩ := cover (List.ofFn (gen k)) ht x (by
    simpa only [List.mem_ofFn', Set.ofPred_mem_eq] using hx)
  exact ⟨⟨n, by simpa using hn⟩, he⟩

set_option maxRecDepth 8192 in
theorem short_test (k : Fin 2) : ∀ x : Fin 2058,
    (∀ i : Fin 3, perm k ⟨i.val, by omega⟩ x = x ∨
      perm k ⟨i.val, by omega⟩ x = perm k 3 x) → perm k 3 x = x := by
  fin_cases k <;> apply Held.TwoLocalCandidates.Cores.allLetters <;> decide +kernel

@[expose] def witness (k : Fin 2) (t : Fin 3) : Fin 2058 :=
  if t = 0 then 44 else if t = 1 then 260 else if k = 0 then 379 else 352

@[expose] def partner (k : Fin 2) (t : Fin 3) : Fin 2058 :=
  if t = 0 then 1010 else if t = 1 then 1750 else if k = 0 then 512 else 1241

set_option maxRecDepth 8192 in
theorem witness_checks : ∀ k : Fin 2, ∀ t : Fin 3,
    witness k t ≠ partner k t ∧
    (∀ n : Fin 16, permForm k n (witness k t) = witness k t ∨
      permForm k n (witness k t) = partner k t) ∧
    ∃ i : Fin 4, perm k i (witness k t) = partner k t := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem separation_check : ∀ k : Fin 2, ∀ n : Fin 16,
    (∀ t : Fin 3, permForm k n (witness k t) = witness k t) → n = 0 ∨ n = 8 := by
  decide +kernel

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankFourKernel

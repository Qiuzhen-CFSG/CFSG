module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# The nine-point permutation image for the Thompson centralizer

The candidate four-space action gives two even permutations. We invert the
right-action point maps so that matrix multiplication agrees with Lean's
left-action permutation multiplication. The permutations below generate A₉:
every three-cycle is exhibited as a word, checked by kernel reduction.

The connection to the 248-dimensional matrices is a separate obligation.
Source program and exploratory subquotient witnesses: `source/README.md`.
-/

namespace Thompson.InvolutionCentralizer.AlternatingQuotient

/-- The inverse of the corresponding right-action point map. -/
@[expose] public def permA : Equiv.Perm (Fin 9) where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6, 8]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

public theorem permA_even : permA ∈ alternatingGroup (Fin 9) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

/-- The inverse of the corresponding right-action point map. -/
@[expose] public def permB : Equiv.Perm (Fin 9) where
  toFun := ![0, 8, 1, 5, 2, 3, 4, 6, 7]
  invFun := ![0, 2, 4, 5, 6, 3, 7, 8, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

public theorem permB_even : permB ∈ alternatingGroup (Fin 9) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private def letter : Fin 4 → Equiv.Perm (Fin 9) :=
  ![permA, permB, permA⁻¹, permB⁻¹]

private def star (a b : Fin 9) : Equiv.Perm (Fin 9) :=
  Equiv.swap 0 a * Equiv.swap a b

private def starWord : Fin 9 → Fin 9 → List (Fin 4) :=
  ![
    ![[], [], [], [], [], [], [], [], []],
    ![[], [], [0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 3, 0, 1], [0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1], [0, 1, 1, 0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 3, 0, 3, 3, 0], [1, 0, 3, 0, 3, 0, 3, 3, 0, 3, 3, 0, 1, 0, 3, 3], [1, 1, 0, 3, 3, 0, 1, 0, 3, 0, 1, 1, 0, 1], [0, 3, 0, 3, 3, 0, 1, 0, 3, 0, 1, 1, 0, 3, 3, 0], [0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 3]],
    ![[], [3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0], [], [0, 3, 0, 3, 0, 3, 3, 0, 3, 3, 0, 1, 0, 3], [1, 0, 1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1, 1, 0, 3], [3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1], [1, 0, 1, 0, 3, 3, 0, 1, 1, 0, 1, 0, 3, 3, 0, 3], [0, 3, 0, 3, 0, 3, 3, 0, 1, 1, 0, 1, 1, 0], [3, 0, 3, 0, 3, 3, 0, 1, 0, 3, 0, 1, 1, 0, 3, 3, 0, 1]],
    ![[], [3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 0], [1, 0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 3, 0, 3], [], [1, 0, 3, 3, 0, 1, 0, 1, 1, 1, 0, 3, 3, 0, 1, 0, 3, 0], [0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 3, 3, 0, 1, 0, 1, 1, 1, 0], [3, 0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 3, 0, 1], [0, 1, 1, 1, 0, 3, 3, 0, 1, 0, 3, 0, 1, 0, 3, 3, 0, 1], [1, 1, 1, 0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 1, 1]],
    ![[], [0, 1, 0, 3, 0, 3, 0, 3, 3, 0, 3, 3, 0, 1, 0, 3, 3, 0], [1, 0, 1, 1, 1, 0, 1, 0, 3, 0, 3, 3, 0, 3, 0, 3], [0, 1, 0, 3, 0, 1, 1, 0, 1, 1, 1, 0, 3, 0, 1, 1, 0, 3], [], [0, 1, 0, 1, 0, 3, 0, 3, 3, 0, 1, 0], [0, 1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1, 1, 0], [0, 1, 0, 3, 3, 0, 1, 1, 0, 1, 0, 3, 3, 0], [0, 1, 0, 1, 0, 3, 0, 1, 1, 0, 1, 1, 0, 1]],
    ![[], [1, 1, 0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 3, 0, 3, 3], [3, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 0, 1], [0, 1, 1, 1, 0, 3, 0, 1, 1, 0, 1, 1, 1, 0, 3, 3, 0, 3, 3, 0], [0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 3, 0], [], [0, 3, 3, 0, 1, 0, 1, 1, 1, 0, 3, 3, 0, 1, 0, 3, 0, 1], [3, 3, 0, 3, 0, 1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 1], [0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 0, 3]],
    ![[], [3, 0, 3, 3, 0, 1, 0, 3, 0, 1, 1, 0, 3, 3], [1, 0, 1, 1, 0, 3, 0, 3, 3, 0, 1, 1, 0, 3, 0, 3], [3, 0, 1, 0, 1, 0, 3, 0, 3, 3, 0, 1, 0, 1], [0, 1, 1, 1, 0, 1, 0, 3, 0, 3, 3, 0, 3, 0], [0, 1, 1, 0, 3, 0, 1, 0, 3, 0, 1, 1, 0, 1, 1, 1, 0, 3], [], [3, 0, 1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1, 1, 0, 1], [3, 0, 1, 0, 3, 3, 0, 1, 1, 0, 1, 0, 3, 3, 0, 1]],
    ![[], [0, 1, 1, 0, 3, 3, 0, 1, 0, 3, 0, 1, 1, 0, 1, 0], [0, 3, 3, 0, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3], [3, 0, 1, 1, 0, 3, 0, 1, 0, 3, 0, 1, 1, 0, 1, 1, 1, 0], [0, 1, 1, 0, 3, 0, 3, 3, 0, 1, 1, 0, 3, 0], [3, 3, 0, 1, 0, 1, 0, 3, 0, 3, 3, 0, 1, 0, 1, 1], [3, 0, 1, 1, 1, 0, 1, 0, 3, 0, 3, 3, 0, 3, 0, 1], [], [3, 3, 0, 1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 1, 1, 0, 1, 1]],
    ![[], [1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 3, 0], [3, 0, 1, 1, 0, 3, 3, 0, 1, 0, 3, 0, 1, 1, 0, 1, 0, 1], [1, 1, 0, 3, 0, 3, 0, 3, 3, 0, 3, 3, 0, 1, 0, 1, 1, 1], [1, 1, 1, 0, 3, 3, 0, 1, 0, 3, 0, 1, 1, 0], [1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0], [3, 0, 1, 1, 0, 3, 0, 3, 3, 0, 1, 1, 0, 3, 0, 1], [3, 3, 0, 1, 1, 1, 0, 1, 0, 3, 0, 3, 3, 0, 3, 0, 1, 1], []]
  ]

private def starCheck : Bool :=
  (List.finRange 9).all fun a => (List.finRange 9).all fun b =>
    if a == 0 || b == 0 || a == b then true else
      (List.finRange 9).all fun t =>
        decide (((starWord a b).map letter).prod t = star a b t)

set_option maxRecDepth 4096 in
private theorem starCheck_eq_true : starCheck = true := by
  decide +kernel

private theorem starWord_spec (a b : Fin 9) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) : ((starWord a b).map letter).prod = star a b := by
  have h := starCheck_eq_true
  simp only [starCheck, List.all_eq_true, List.mem_finRange, forall_const] at h
  specialize h a b
  have hn : (a == 0 || b == 0 || a == b) = false := by simp [ha, hb, hab]
  rw [hn] at h
  simp only [Bool.false_eq_true, ↓reduceIte, List.all_eq_true, List.mem_finRange,
    forall_const, decide_eq_true_eq] at h
  exact Equiv.ext h

private theorem threeCycle_formula : ∀ a b c : Fin 9, a ≠ b → b ≠ c → a ≠ c →
    Equiv.swap a b * Equiv.swap b c =
      if a = 0 then star b c else if b = 0 then (star a c)⁻¹
      else if c = 0 then star a b else star a b * star b c := by
  decide +kernel

/-- Every subgroup containing the two candidate image generators contains A₉. -/
public theorem alternating_le_of_generators (H : Subgroup (Equiv.Perm (Fin 9)))
    (ha : permA ∈ H) (hb : permB ∈ H) : alternatingGroup (Fin 9) ≤ H := by
  have hs (a b : Fin 9) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b) : star a b ∈ H := by
    rw [← starWord_spec a b ha0 hb0 hab]
    apply H.list_prod_mem
    intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    fin_cases i
    · exact ha
    · exact hb
    · exact H.inv_mem ha
    · exact H.inv_mem hb
  have hcycle (a b c : Fin 9) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
      Equiv.swap a b * Equiv.swap b c ∈ H := by
    rw [threeCycle_formula a b c hab hbc hac]
    split_ifs with ha0 hb0 hc0
    · exact hs b c (ha0 ▸ hab.symm) (ha0 ▸ hac.symm) hbc
    · exact H.inv_mem (hs a c ha0 (hb0 ▸ hbc.symm) hac)
    · exact hs a b ha0 hb0 hab
    · exact H.mul_mem (hs a b ha0 hb0 hab) (hs b c hb0 hc0 hbc)
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro g hg
  obtain ⟨a, ha'⟩ := hg.isCycle.nonempty_support
  have he := (hg.eq_swap_mul_swap_iff_mem_support).mpr ha'
  have hn := (hg.nodup_iff_mem_support).mpr ha'
  have hab : a ≠ g a := by simpa using (Equiv.Perm.mem_support.mp ha').symm
  have hbc : g a ≠ g (g a) := g.injective.ne hab
  have hac : a ≠ g (g a) := by
    intro heq
    exact (List.nodup_cons.mp hn).1
      (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr heq)))
  rw [he]
  exact hcycle a (g a) (g (g a)) hab hbc hac

/-- Exact identification of the subgroup generated by the two point maps. -/
public theorem closure_generators :
    Subgroup.closure {permA, permB} = alternatingGroup (Fin 9) := by
  apply le_antisymm
  · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨permA_even, permB_even⟩
  · exact alternating_le_of_generators _
      (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

end Thompson.InvolutionCentralizer.AlternatingQuotient

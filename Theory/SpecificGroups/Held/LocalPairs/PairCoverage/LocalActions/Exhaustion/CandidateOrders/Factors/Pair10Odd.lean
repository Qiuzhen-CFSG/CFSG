module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair10OddRelations
import Mathlib.Tactic.FinCases

/-!
# The order of a literal Held candidate

Collection gives the upper bound; distinct literal words give the lower bound.
The proposed data comes from the unchanged ATLAS degree-2058 carrier and
LocalActions/Candidates.lean. The Lean kernel checks every used identity.
See source/generate.py for reproduction; GAP output is not a premise.
-/

set_option maxRecDepth 16384
set_option Elab.async false

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair10Odd
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors

private theorem triangular_1 : triangular
    (([1] : List (Fin 2)).map (fun p => (pc p, relativeOrder p))) := by
  apply triangular_cons_words pc relativeOrder 1 [] (by decide)
    (powerWord 1) (conjugateWord 1) (power_1)
  · intro b hb
    exact False.elim (List.not_mem_nil hb)
  · decide +kernel
  · decide +kernel
  · trivial

private theorem triangular_0 : triangular
    (([0, 1] : List (Fin 2)).map (fun p => (pc p, relativeOrder p))) := by
  apply triangular_cons_words pc relativeOrder 0 [1] (by decide)
    (powerWord 0) (conjugateWord 0) (power_0)
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl
    · exact conj_0_1
  · decide +kernel
  · decide +kernel
  · exact triangular_1

theorem upper_bound : Nat.card (Subgroup.closure (Set.range input)) ≤ 9 := by
  have hpc : Nat.card (Subgroup.closure (Set.range pc)) ≤ 9 := by
    have h := card_le _ triangular_0
    have he : Prod.fst '' {x | x ∈ ([0, 1] : List (Fin 2)).map
        (fun p => (pc p, relativeOrder p))} = Set.range pc := by
      ext x
      simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨k, _, rfl⟩, rfl⟩
        exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩
        refine ⟨(pc k, relativeOrder k), ⟨k, ?_, rfl⟩, rfl⟩
        fin_cases k <;> simp
    rw [he] at h
    exact h
  have hle : Subgroup.closure (Set.range input) ≤ Subgroup.closure (Set.range pc) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k,rfl⟩
    have hi : input k = ((inputWord k).map pc).prod := by
      fin_cases k
      · exact input_0
      · exact input_1
    rw [hi]
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hx
    exact Subgroup.subset_closure (Set.mem_range_self t)
  exact (Subgroup.card_le_of_le hle).trans hpc

def radix : Fin 2 → ℕ
  | 0 => 1
  | 1 => 3

def normalForm (v : Fin 9) : He :=
  (List.ofFn (fun k : Fin 2 => pc k ^ (v.val / radix k % relativeOrder k))).prod

def normalTable (v : Fin 9) : Equiv.Perm (Fin 2058) :=
  (List.ofFn (fun k : Fin 2 => pcTable k ^ (v.val / radix k % relativeOrder k))).prod

theorem normalTable_eq (v : Fin 9) : normalTable v = representation (normalForm v) := by
  simp only [normalForm, normalTable, map_list_prod, List.map_ofFn, Function.comp_def, map_pow, ← pcTable_eq]

def decodeCode (x : ℕ) : ℕ :=
  (if x < 864 then (if x < 363 then (if x < 291 then 0 else 1) else (if x < 841 then 2 else 5)) else (if x < 1348 then (if x < 928 then 7 else 3) else (if x < 1417 then 4 else (if x < 1657 then 6 else 8))))

def decode (g : Equiv.Perm (Fin 2058)) : ℕ := decodeCode (0 * 2058 + (g 0).val)

abbrev decode_normalPredicate (x : Fin 9) : Prop := decode (normalTable x) = x.val

private theorem decode_normal_block0 : checkFin 64 (fun j => decide (decode_normalPredicate (blockIndex 9 64 (by decide) 0 j.val))) = true := by decide +kernel

theorem decode_normal : ∀ x, decode_normalPredicate x := by
  apply allBlocks (b := 1) (m := 64) (by decide) (by decide) (by decide)
  intro k
  fin_cases k
  · exact allFin _ _ decode_normal_block0

theorem order : Nat.card (Subgroup.closure (Set.range input)) = 9 := by
  apply Nat.le_antisymm upper_bound
  apply lower_bound _ 9 normalForm (fun x => decode (representation x))
  · intro v
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hx
    apply Subgroup.pow_mem
    exact evalSigned_mem input (pcWord k) _
      (fun i => Subgroup.subset_closure (Set.mem_range_self i))
  · intro v
    rw [← normalTable_eq]
    exact decode_normal v

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair10Odd

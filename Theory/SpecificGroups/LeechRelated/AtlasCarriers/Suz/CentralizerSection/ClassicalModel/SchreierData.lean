module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.ClassicalModel.Action

/-!
# Short transversal words for the singular-basis stabilizer chain

At each of the first five basis positions, the table supplies words in the
two literal isometries that fix the preceding basis vectors and move the
current vector to each admissible image. Admissibility uses quadratic values,
polar pairings and distinctness. The final vector has only two possibilities.
All coverage and word-action assertions are checked in the Lean kernel.

The word search is an untrusted means of finding witnesses, reproduced in
`ClassicalModel/source/generate_transversals.py`. The proof consumes only the
certificates stated here. Source motivation: GLS3 Table 5.3o and the quadratic
isometry convention of section 2.7.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Suz.CentralizerSection.ClassicalModel

def basisVector (j : Fin 6) : V := Pi.single j 1

def polar (v w : V) : K := form (v+w) - form v - form w

def admissible (k : Fin 6) (v : V) : Prop :=
  v ≠ 0 ∧ form v = 0 ∧ ∀ j : Fin 6, j.val < k.val →
    v ≠ basisVector j ∧ polar v (basisVector j) = polar (basisVector k) (basisVector j)
instance (k : Fin 6) (v : V) : Decidable (admissible k v) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def wordEval (w : String) : O :=
  (w.toList.map fun a => if a = 'c' then cIsometry else dIsometry).prod

def wordPermutation (w : String) : Equiv.Perm (Fin 27) :=
  (w.toList.map fun a => if a = 'c' then blockC else blockD).prod

theorem wordEval_mem (w : String) : wordEval w ∈ generated := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem wordEval_action (w : String) : orthogonalAction (wordEval w) = wordPermutation w := by
  simp only [wordEval, wordPermutation, map_list_prod, List.map_map]
  congr 2
  funext a
  by_cases ha : a = 'c'
  · simp [ha, orthogonalAction_c]
  · simp [ha, orthogonalAction_d]

def transversal (k : Fin 5) (i : Fin 27) : String :=
  match k.val, i.val with
  | 0, 1 => "cddcc"
  | 0, 18 => "dccddcc"
  | 0, 2 => "ccdcd"
  | 0, 15 => "cccdcc"
  | 0, 3 => "ccc"
  | 0, 9 => "cddccc"
  | 0, 16 => "cdcd"
  | 0, 6 => "cd"
  | 0, 4 => "cccc"
  | 0, 23 => "ddcc"
  | 0, 8 => "dccc"
  | 0, 5 => "cdccc"
  | 0, 12 => "ccccd"
  | 0, 22 => "ccdcc"
  | 0, 7 => "ccddcc"
  | 0, 21 => "c"
  | 0, 14 => "d"
  | 0, 17 => "ccd"
  | 0, 13 => "dcc"
  | 0, 25 => "cccd"
  | 0, 10 => "ccccdcc"
  | 0, 11 => "dcd"
  | 0, 24 => "ddccc"
  | 0, 26 => "cc"
  | 0, 19 => "ddcd"
  | 0, 20 => "cdcc"
  | 1, 18 => "ccccdc"
  | 1, 16 => "dcccdccd"
  | 1, 6 => "dcdddcc"
  | 1, 8 => "ccdcdcdc"
  | 1, 5 => "cdcdcd"
  | 1, 14 => "dccdcddcd"
  | 1, 17 => "cdcccdccc"
  | 1, 19 => "dddcdddcc"
  | 1, 20 => "dddcccdccd"
  | 2, 15 => "ccddcccc"
  | 2, 12 => "ddccccddddc"
  | 2, 22 => "cddddccddc"
  | 2, 13 => "ccccddddc"
  | 2, 25 => "ddccccddc"
  | 2, 10 => "cddcddccddcc"
  | 2, 11 => "ccccddc"
  | 3, 4 => "dddd"
  | 3, 21 => "cdccdcdccd"
  | 3, 24 => "dd"
  | 4, 21 => "dcddddccccdcc"
  | 4, 24 => "ddddccddcddcccc"
  | _, _ => ""

theorem transversal_spec : ∀ k : Fin 5, ∀ i : Fin 27,
    admissible k.castSucc (pointVector i) →
      wordPermutation (transversal k i) (basisIndex k.castSucc) = i ∧
      ∀ j : Fin 6, j.val < k.val →
        wordPermutation (transversal k i) (basisIndex j) = basisIndex j := by
  decide +kernel

theorem terminal_vectors : ∀ i : Fin 27,
    admissible 5 (pointVector i) → i = 7 ∨ i = 26 := by
  decide +kernel

end Sporadic.LeechRelated.Suz.CentralizerSection.ClassicalModel

module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Evaluation
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Tables0
import Mathlib.Tactic.FinCases

/-!
# Permutation evaluation of the Held transition words

These equations transport the literal Held words through their faithful
representation. The already certified ATLAS max3 generator table avoids
repeated expansion of its twelve-letter word. This is a computational view
of the existing carrier, with no separate group or recognition assumption.
Source: `Held.Model.Basic`, `TwoLocalCandidates.Cores.Tables0`, and the
unchanged word data described in `DoubleCosets/source/README.md`.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets

set_option maxRecDepth 4096 in
/-- Literal words for the three fixed additional elements. -/
public theorem move_eq_word : move = fun i => wordEval a b (moveWord i) := by
  funext i
  fin_cases i <;> simp only [move, representative_eq_fast] <;>
    congr 1

@[expose] public def markedPermutation (i : Fin 4) : Equiv.Perm (Fin 2058) :=
  wordEval atlasA Held.TwoLocalCandidates.Cores.Tables0.p1 (generatorWords i)

public theorem representation_markedGenerator (i : Fin 4) :
    representation (markedGenerator i) = markedPermutation i := by
  have h : Held.TwoLocalCandidates.Cores.Tables0.p1 =
      representation (localWord false) := Held.TwoLocalCandidates.Cores.Tables0.p1_eq
  rw [markedGenerator, map_wordEval, ← h]
  rfl

@[expose] public def movePermutation (i : Fin 3) : Equiv.Perm (Fin 2058) :=
  wordEval atlasA atlasB (moveWord i)

public theorem representation_move (i : Fin 3) :
    representation (move i) = movePermutation i := by
  rw [move_eq_word, map_wordEval]
  rfl

@[expose] public def middlePermutation (i : Fin 3) (e : Bool) : Equiv.Perm (Fin 2058) :=
  if e then markedPermutation (toggleIndex i) else 1

public theorem representation_middle (i : Fin 3) (e : Bool) :
    representation (middle i e) = middlePermutation i e := by
  cases e
  · exact representation.map_one
  · exact representation_markedGenerator _

@[expose] public def permutationGenerator (i : Fin 7) : Equiv.Perm (Fin 2058) :=
  Fin.addCases (motive := fun _ : Fin (4 + 3) => Equiv.Perm (Fin 2058))
    markedPermutation movePermutation i

public theorem representation_generator (i : Fin 7) :
    representation (generator i) = permutationGenerator i := by
  refine Fin.addCases (n := 3) (m := 4) (fun j => ?_) (fun j => ?_) i
  · simpa only [generator, permutationGenerator, Fin.addCases_left] using
      representation_markedGenerator j
  · simpa only [generator, permutationGenerator, Fin.addCases_right] using
      representation_move j

public theorem representation_eval {n : ℕ} (gen : Fin n → He) (w : List (Fin n × ℤ)) :
    representation (eval gen w) = (w.map fun p => representation (gen p.1) ^ p.2).prod := by
  simp only [eval, map_list_prod, List.map_map, Function.comp_def, map_zpow]

public theorem representation_representative (i : Fin 4831) :
    representation (representative i) = wordEval atlasA atlasB (fastRepresentativeWord i) := by
  rw [representative_eq_fast, map_wordEval]
  rfl

public theorem representation_subgroupElement (i : Fin 1024) :
    representation (subgroupElement i) = ((subgroupWord i).map markedPermutation).prod := by
  simp only [subgroupElement, map_list_prod, List.map_map, Function.comp_def,
    representation_markedGenerator]

end Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets

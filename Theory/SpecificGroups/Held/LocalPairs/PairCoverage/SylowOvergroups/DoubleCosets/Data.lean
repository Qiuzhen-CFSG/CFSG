module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Tests
public import Theory.GroupTheory.DoubleCosetTransitions

/-!
# Short transitions for the fixed Held double-coset representatives

The three additional generators are the unchanged representatives with indices
1, 9, 4279. The two middle factors for each are the identity and one marked
generator. Separate proofs certify generation, the two-coset splitting, and
all 28,986 transitions. `TransitionColumn` is a finite family of actual
factorization obligations, independent of representative obstruction tests.

The recovery and splitting words were found in the literal ATLAS carrier by
GAP. They are candidate data only until their equations have been checked.
See `source/README.md`, `source/recovery.json`, and `source/split.json`.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets
open Theory.GroupTheory.DoubleCosetTransitions

def move : Fin 3 → He
  | 0 => representative 1
  | 1 => representative 9
  | 2 => representative 4279

/-- Literal signed words for the three fixed moves, avoiding repeated decoding.
The equality with `move` is proved in `PermutationEvaluation`. -/
def moveWord : Fin 3 → List (Bool × ℤ)
  | 0 => [(Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 1), (Bool.false, Int.negSucc 0), (Bool.true, Int.ofNat 2), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 1), (Bool.false, Int.negSucc 0), (Bool.true, Int.ofNat 2), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 1), (Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 3), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 1), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 2), (Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 1), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 1), (Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 1), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 0), (Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 2), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 2), (Bool.false, Int.negSucc 0), (Bool.true, Int.ofNat 1), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 1), (Bool.false, Int.negSucc 0), (Bool.true, Int.ofNat 2), (Bool.false, Int.negSucc 0), (Bool.true, Int.ofNat 1), (Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 3), (Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 3), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 0), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 1), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 2), (Bool.false, Int.negSucc 1), (Bool.true, Int.negSucc 1), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 0), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 2), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 2), (Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 3), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 1), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 0)]
  | 1 => [(Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 2), (Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 3), (Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 2), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 3), (Bool.false, Int.negSucc 0), (Bool.true, Int.ofNat 1), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 1), (Bool.false, Int.negSucc 0), (Bool.true, Int.ofNat 3), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 1), (Bool.false, Int.negSucc 0), (Bool.true, Int.ofNat 1), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 0), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 0), (Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 1), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 0), (Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 2), (Bool.false, Int.negSucc 0), (Bool.true, Int.ofNat 2), (Bool.false, Int.negSucc 0), (Bool.true, Int.ofNat 1), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 0), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 1), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 0)]
  | 2 => [(Bool.true, Int.ofNat 2), (Bool.false, Int.negSucc 0), (Bool.true, Int.ofNat 1), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 1), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 2), (Bool.false, Int.negSucc 0), (Bool.true, Int.negSucc 0), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 0), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 0), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 1), (Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 1), (Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 2), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 0), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 0), (Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 2), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 0), (Bool.false, Int.negSucc 0), (Bool.true, Int.ofNat 2), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 1), (Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 2), (Bool.false, Int.ofNat 1), (Bool.true, Int.negSucc 1), (Bool.false, Int.ofNat 1), (Bool.true, Int.ofNat 2)]

def toggleIndex : Fin 3 → Fin 4
  | 0 => 2
  | 1 => 0
  | 2 => 3

def middle (i : Fin 3) (e : Bool) : He :=
  if e then markedGenerator (toggleIndex i) else 1

theorem middle_mem (i : Fin 3) (e : Bool) : middle i e ∈ markedSubgroup := by
  cases e
  · exact markedSubgroup.one_mem
  · exact markedGenerator_mem _

/-- The four marked generators followed by the three additional elements. -/
def generator (i : Fin 7) : He :=
  Fin.addCases (motive := fun _ : Fin (4 + 3) => He) markedGenerator move i

def eval {n : ℕ} (gen : Fin n → He) (w : List (Fin n × ℤ)) : He :=
  (w.map fun p => gen p.1 ^ p.2).prod

theorem eval_mem {n : ℕ} (gen : Fin n → He) (K : Subgroup He)
    (hgen : ∀ i, gen i ∈ K) (w : List (Fin n × ℤ)) : eval gen w ∈ K := by
  apply K.list_prod_mem
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
  exact K.zpow_mem (hgen p.1) p.2

def recoveryA : List (Fin 7 × ℤ) := [(2, -1), (0, -1), (3, -2), (6, 2), (4, 1), (6, 1), (5, -1), (0, -1), (4, -1), (5, -1), (0, -1), (4, -1), (5, -1), (4, -1), (5, -1), (6, -1), (4, -1)]

def recoveryB : List (Fin 7 × ℤ) := [(5, 1), (6, 1), (5, 1), (0, 1), (4, 1), (5, 1), (4, 1), (5, -1), (6, 2), (5, 1), (4, 1), (3, 1), (2, 2), (1, 1), (3, 2), (6, 1), (5, 1), (4, 1), (0, 1), (4, 1), (1, 1), (2, 2), (1, 1), (2, 1), (6, 1), (4, 1), (5, 1), (4, 1), (0, 1), (5, 1), (6, 1), (4, 1), (5, -1), (4, 1), (5, -1), (6, 1), (5, 1), (0, 1), (1, 1), (0, 1), (2, 1), (5, 1), (2, 1), (5, 1), (4, 1), (5, 1), (0, 1), (5, 1), (3, 2), (6, 1), (3, 1), (4, 1), (6, -1), (5, -1), (0, -1), (2, 1), (3, 1), (4, 1), (5, 1), (0, 1), (1, 1), (0, 1), (3, 1), (4, 1)]

/-- The next middle factor when multiplying on the left by a marked generator. -/
def splitNext (i : Fin 3) (j : Fin 4) (e : Bool) : Bool :=
  if j = toggleIndex i then !e else e

/-- Words for the conjugated correction in each of the 24 small transitions. -/
def splitWord : Fin 3 → Fin 4 → Bool → List (Fin 4 × ℤ)
  | 0, 0, false => [(1, -1), (3, -1), (2, -1), (0, -1), (2, -1), (1, -1), (0, -1), (3, -1)]
  | 0, 0, true => [(3, -3), (2, -1), (0, 1), (2, 1), (3, -1)]
  | 0, 1, false => [(1, -1), (3, -2)]
  | 0, 1, true => [(1, -1), (3, -2)]
  | 0, 2, false => []
  | 0, 2, true => []
  | 0, 3, false => [(3, 1)]
  | 0, 3, true => [(3, -1)]
  | 1, 0, false => []
  | 1, 0, true => []
  | 1, 1, false => [(2, -1)]
  | 1, 1, true => [(1, -1), (3, -3), (2, -1), (0, -1), (2, -1), (1, -1), (0, -1), (3, -1), (0, -1), (2, -1), (0, -1)]
  | 1, 2, false => [(1, -1)]
  | 1, 2, true => [(3, -1), (0, 1), (2, 1), (0, 1), (3, 1)]
  | 1, 3, false => [(2, 1), (3, 1), (1, 1)]
  | 1, 3, true => [(0, 1), (1, 1), (0, 1), (2, -1), (0, -1), (3, 1), (0, -1), (3, 1), (1, 1)]
  | 2, 0, false => [(3, -3), (2, -1), (0, 1), (1, 1), (0, 1), (2, 1), (0, -1), (1, -1), (3, -1), (0, -1)]
  | 2, 0, true => [(3, -3), (0, 1), (3, -1)]
  | 2, 1, false => [(0, -1), (1, -1), (0, -1)]
  | 2, 1, true => [(1, -1), (3, -2), (2, -1), (0, 1), (1, 1), (0, 1), (2, 1)]
  | 2, 2, false => [(0, -1), (2, -1), (1, -1), (0, -1)]
  | 2, 2, true => [(3, -2), (0, -1), (2, -1), (1, -1), (0, -1), (1, -1)]
  | 2, 3, false => []
  | 2, 3, true => [(1, -1), (3, -2), (2, -1), (0, 1), (1, 1), (0, 1), (2, 1), (0, -1), (1, -1), (0, -1)]

/-- One of the three independent finite transition calculations. -/
def TransitionColumn (i : Fin 3) : Prop :=
  ∀ j : Fin 4831, ∀ e : Bool,
    Covered markedSubgroup representative (representative j * middle i e * move i)

end Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets

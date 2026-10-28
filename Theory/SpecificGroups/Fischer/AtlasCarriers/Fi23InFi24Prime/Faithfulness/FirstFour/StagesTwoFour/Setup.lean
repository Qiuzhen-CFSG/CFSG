module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.PointChecks
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Data
public import Theory.GroupAction.GeneratorStabilizerReduction

/-!
# Literal right-coset tables for the two middle reductions

The representative at a vertex is the positive word along its BFS path.
The table's positive edges describe the inverse action on labels, so their
Schreier elements are `rep j * gen a * (rep (next j))⁻¹`. Keeping this
orientation explicit avoids confusing right-coset words with left actions.

`InverseAction` and `NonTreeEdges` are the two remaining mathematical inputs.
The finite table and its tree equations are checked separately; neither input
is inferred from an experimental order. Source: ATLAS F24G1-p306936B0,
GLS3 Table 5.3v, and the retained `source/faithfulness/nodes.json`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour

abbrev Ambient := Equiv.Perm (Fin 306936)

def size (i : Fin 2) : Nat := if i = 0 then 3159 else 630

theorem size_pos (i : Fin 2) : 0 < size i := by fin_cases i <;> decide

def root (i : Fin 2) : Fin (size i) := ⟨0, size_pos i⟩

def labelRaw (i : Fin 2) : Nat → Nat := if i = 0 then Data.label2 else Data.label3

def label (i : Fin 2) (j : Fin (size i)) : Fin 306936 :=
  ⟨labelRaw i j.val % 306936, Nat.mod_lt _ (by decide)⟩

def stepRaw (i a : Fin 2) : Nat → Nat :=
  if i = 0 then if a = 0 then Data.step02 else Data.step12
  else if a = 0 then Data.step03 else Data.step13

def backRaw (i a : Fin 2) : Nat → Nat :=
  if i = 0 then if a = 0 then Data.back02 else Data.back12
  else if a = 0 then Data.back03 else Data.back13

def next (i a : Fin 2) (j : Fin (size i)) : Fin (size i) :=
  ⟨stepRaw i a j.val % size i, Nat.mod_lt _ (size_pos i)⟩

def prev (i a : Fin 2) (j : Fin (size i)) : Fin (size i) :=
  ⟨backRaw i a j.val % size i, Nat.mod_lt _ (size_pos i)⟩

def parentRaw (i : Fin 2) : Nat → Nat := if i = 0 then Data.parent2 else Data.parent3

def parent (i : Fin 2) (j : Fin (size i)) : Fin (size i) :=
  ⟨parentRaw i j.val % size i, Nat.mod_lt _ (size_pos i)⟩

def letterRaw (i : Fin 2) : Nat → Nat := if i = 0 then Data.letter2 else Data.letter3

def letter (i : Fin 2) (j : Fin (size i)) : Fin 2 :=
  ⟨letterRaw i j.val % 2, Nat.mod_lt _ (by decide)⟩

def wordRaw (i : Fin 2) : Nat → Nat := if i = 0 then Data.word2 else Data.word3

/-- Low five bits give the length, followed by one generator bit per letter. -/
def repWord (i : Fin 2) (j : Fin (size i)) : List (Fin 2) :=
  List.ofFn fun k : Fin (wordRaw i j.val % 32) =>
    (⟨(wordRaw i j.val >>> (5 + k.val)) % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2)

def gen (i : Fin 2) : Fin 2 → Ambient := generators (i.natAdd 2)

def representative (i : Fin 2) (j : Fin (size i)) : Ambient :=
  ((repWord i j).map (gen i)).prod

def schreier (i a : Fin 2) (j : Fin (size i)) : Ambient :=
  representative i j * gen i a * (representative i (next i a j))⁻¹

/-- The incoming tree edge at a nonroot vertex. -/
def IsTree (i a : Fin 2) (j : Fin (size i)) : Prop :=
  next i a j ≠ root i ∧ parent i (next i a j) = j ∧ letter i (next i a j) = a

/-- Comparisons at the specified labels with the literal model permutations. -/
def InverseAction : Prop :=
  ∀ (i a : Fin 2) (j : Fin (size i)), (gen i a)⁻¹ (label i j) = label i (next i a j)

/-- Only nontree edges need mathematical membership witnesses. -/
def NonTreeEdges : Prop :=
  ∀ (i a : Fin 2) (j : Fin (size i)), ¬ IsTree i a j →
    schreier i a j ∈ stage (i.natAdd 2).succ

/-- Purely finite checks; no large permutation words are evaluated here. -/
def localTest (i : Fin 2) (n : Nat) : Bool :=
  let j : Fin (size i) := ⟨n % size i, Nat.mod_lt _ (size_pos i)⟩
  decide ((∀ a : Fin 2, prev i a (next i a j) = j ∧ next i a (prev i a j) = j) ∧
    (label i j = label i (root i) → j = root i) ∧
    (j ≠ root i → repWord i j = repWord i (parent i j) ++ [letter i j] ∧
      next i (letter i j) (parent i j) = j ∧ (parent i j).val < j.val))

theorem root_word (i : Fin 2) : repWord i (root i) = [] := by
  fin_cases i <;> rfl

theorem root_representative (i : Fin 2) : representative i (root i) = 1 := by
  simp only [representative, root_word, List.map_nil, List.prod_nil]

theorem point_eq_root_label (i : Fin 2) : point (i.natAdd 2) = label i (root i) := by
  fin_cases i
  · exact point_two
  · exact point_three

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour

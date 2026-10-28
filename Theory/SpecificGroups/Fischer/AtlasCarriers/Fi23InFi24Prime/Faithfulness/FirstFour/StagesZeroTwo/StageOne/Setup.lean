module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.Certificate
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageOne.Data

/-!
# Word representatives for stage one

The rooted tree gives actual positive words in generators 1. Its edge action
is inverse permutation application, so inverse word representatives give the
left representatives required by `PositiveTable`. The words are defined by
recursion on the vertex index, rather than by expanding nested permutations.

`TreeAction` asks only for the 28159 incoming point images. `NonTreeEdges`
asks for membership of the remaining full-degree Schreier permutations in
the literal stage two. Neither premise asserts stabilizer recognition.

Source: ATLAS F24G1-p306936B0, GLS3 Table 5.3v; `source/tree.json`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne

abbrev Ambient := Equiv.Perm (Fin 306936)
abbrev Vertex := Fin 28160

def root : Vertex := 0

def label (j : Vertex) : Fin 306936 :=
  ⟨Data.label j.val % 306936, Nat.mod_lt _ (by decide)⟩

def next (a : Fin 2) (j : Vertex) : Vertex :=
  ⟨(if a = 0 then Data.step0 j.val else Data.step1 j.val) % 28160,
    Nat.mod_lt _ (by decide)⟩

def prev (a : Fin 2) (j : Vertex) : Vertex :=
  ⟨(if a = 0 then Data.back0 j.val else Data.back1 j.val) % 28160,
    Nat.mod_lt _ (by decide)⟩

def parentIndex (n : Nat) : Nat := Data.parent n % n

def parent (j : Vertex) : Vertex :=
  ⟨parentIndex j.val % 28160, Nat.mod_lt _ (by decide)⟩

def letterIndex (n : Nat) : Fin 2 := ⟨Data.letter n % 2, Nat.mod_lt _ (by decide)⟩

def letter (j : Vertex) : Fin 2 := letterIndex j.val

/-- The defining positive word follows the immutable parent tree. -/
def path : Nat → List (Fin 2)
  | 0 => []
  | n + 1 => path (parentIndex (n + 1)) ++ [letterIndex (n + 1)]
termination_by n => n
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)

def repWord (j : Vertex) : List (Fin 2) := path j.val

def gen : Fin 2 → Ambient := generators 1

def rightRep (j : Vertex) : Ambient := ((repWord j).map gen).prod

/-- Actual word permutations, with the orientation required by `PositiveTable`. -/
def representative (j : Vertex) : Ambient := (rightRep j)⁻¹

def schreier (a : Fin 2) (j : Vertex) : Ambient :=
  rightRep j * gen a * (rightRep (next a j))⁻¹

def IsTree (a : Fin 2) (j : Vertex) : Prop :=
  next a j ≠ root ∧ parent (next a j) = j ∧ letter (next a j) = a

/-- Forward applications suffice to certify the inverse-action incoming edges. -/
def TreeAction : Prop :=
  ∀ j : Vertex, j ≠ root → gen (letter j) (label j) = label (parent j)

/-- These are memberships of actual permutations on all 306936 letters. -/
def NonTreeEdges : Prop :=
  ∀ (a : Fin 2) (j : Vertex), ¬ IsTree a j → schreier a j ∈ stage 2

/-- Pure finite data checks; no long group word is evaluated here. -/
def localTest (n : Nat) : Bool :=
  let j : Vertex := ⟨n % 28160, Nat.mod_lt _ (by decide)⟩
  decide ((∀ a : Fin 2, prev a (next a j) = j ∧ next a (prev a j) = j) ∧
    (label j = label root → j = root) ∧
    (j ≠ root → next (letter j) (parent j) = j))

theorem root_word : repWord root = [] := by
  simp [repWord, root, path]

theorem root_rightRep : rightRep root = 1 := by
  simp only [rightRep, root_word, List.map_nil, List.prod_nil]

theorem root_representative : representative root = 1 := by
  simp only [representative, root_rightRep, inv_one]

theorem point_eq_root_label : point 1 = label root := point_one

theorem parent_lt (j : Vertex) (hj : j ≠ root) : (parent j).val < j.val := by
  have hn : 0 < j.val := by
    have : j.val ≠ 0 := fun h => hj (Fin.ext h)
    omega
  have hp : parentIndex j.val < j.val := Nat.mod_lt _ hn
  simpa only [parent, Nat.mod_eq_of_lt (lt_trans hp j.isLt)] using hp

theorem repWord_parent (j : Vertex) (hj : j ≠ root) :
    repWord j = repWord (parent j) ++ [letter j] := by
  have hn : 0 < j.val := by
    have : j.val ≠ 0 := fun h => hj (Fin.ext h)
    omega
  have hp : parentIndex j.val < 28160 := lt_trans (Nat.mod_lt _ hn) j.isLt
  obtain ⟨n, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  change path j.val = path (parentIndex j.val % 28160) ++ [letterIndex j.val]
  rw [Nat.mod_eq_of_lt hp, he, path]

theorem rightRep_parent (j : Vertex) (hj : j ≠ root) :
    rightRep j = rightRep (parent j) * gen (letter j) := by
  simp only [rightRep, repWord_parent j hj, List.map_append, List.prod_append,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageOne

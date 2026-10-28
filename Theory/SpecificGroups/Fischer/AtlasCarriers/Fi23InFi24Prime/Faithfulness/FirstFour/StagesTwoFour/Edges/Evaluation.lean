module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Setup

/-!
# Evaluation of cached middle-stage words

The alphabet consists of the eight literal words at stages two, three and four.
A signed numerical evaluator agrees with their ordinary permutation product
once each cached letter has been compared on the entire ambient set. The
comparison is an explicit premise, never a consequence of a small orbit table.
Source: ATLAS F24G1-p306936B0 and the retained `source/faithfulness/nodes.json`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.Edges

abbrev Letter := Fin 8 × Bool
abbrev NumericalMaps := Fin 8 → Bool → Nat → Nat

/-- `true` means a positive letter. -/
def literal : Fin 8 → Ambient
  | 0 => Word.word11 aPerm bPerm
  | 1 => Word.word14 aPerm bPerm
  | 2 => Word.word17 aPerm bPerm
  | 3 => Word.word20 aPerm bPerm
  | 4 => Word.word23 aPerm bPerm
  | 5 => Word.word26 aPerm bPerm
  | 6 => Word.word29 aPerm bPerm
  | 7 => Word.word32 aPerm bPerm

def signed (c : Letter) : Ambient := if c.2 then literal c.1 else (literal c.1)⁻¹

def evaluate (w : List Letter) : Ambient := (w.map signed).prod

/-- Force an intermediate numerical value before the next table lookup. -/
def force (x : Nat) (f : Nat → Nat) : Nat :=
  match x with
  | 0 => f 0
  | n + 1 => f (n + 1)

theorem force_eq (x : Nat) (f : Nat → Nat) : force x f = f x := by cases x <;> rfl

def evaluateNat (f : NumericalMaps) : List Letter → Nat → Nat
  | [], x => x
  | c :: w, x => force (evaluateNat f w x) (f c.1 c.2)

/-- Every sign and every ambient point must be compared with the literal model. -/
def MapsCorrect (f : NumericalMaps) : Prop :=
  ∀ (c : Letter) (x : Fin 306936), f c.1 c.2 x.val = (signed c x).val

theorem evaluateNat_correct (f : NumericalMaps) (hf : MapsCorrect f)
    (w : List Letter) (x : Fin 306936) :
    evaluateNat f w x.val = (evaluate w x).val := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [evaluateNat, force_eq, ih, hf]
    rfl

theorem evaluate_append (u v : List Letter) :
    evaluate (u ++ v) = evaluate u * evaluate v := by
  simp only [evaluate, List.map_append, List.prod_append]

def currentIndex : Fin 2 → Fin 2 → Fin 8
  | 0, 0 => 0
  | 0, 1 => 1
  | 1, 0 => 2
  | 1, 1 => 3

/-- Padding duplicates the two generators at stage three. -/
def nextIndex : Fin 2 → Fin 4 → Fin 8
  | 0, 0 => 2
  | 0, 1 => 3
  | 0, 2 => 2
  | 0, 3 => 3
  | 1, 0 => 4
  | 1, 1 => 5
  | 1, 2 => 6
  | 1, 3 => 7

theorem currentIndex_eq (i a : Fin 2) : literal (currentIndex i a) = gen i a := by
  fin_cases i <;> fin_cases a <;> rfl

theorem nextIndex_mem (i : Fin 2) (a : Fin 4) :
    literal (nextIndex i a) ∈ stage (i.natAdd 2).succ := by
  fin_cases i <;> fin_cases a <;> apply Subgroup.subset_closure <;>
    simp [nextIndex, literal, Word.generators]

def representativeWord (i : Fin 2) (j : Fin (size i)) : List Letter :=
  (repWord i j).map fun a => (currentIndex i a, true)

theorem representativeWord_eq (i : Fin 2) (j : Fin (size i)) :
    evaluate (representativeWord i j) = representative i j := by
  simp only [evaluate, representativeWord, List.map_map, representative]
  congr 1
  apply List.map_congr_left
  intro a _
  exact currentIndex_eq i a

/-- A signed next-stage word always belongs to the literal next subgroup. -/
def factorWord (i : Fin 2) (w : List (Fin 4 × Bool)) : List Letter :=
  w.map fun c => (nextIndex i c.1, c.2)

theorem factorWord_mem (i : Fin 2) (w : List (Fin 4 × Bool)) :
    evaluate (factorWord i w) ∈ stage (i.natAdd 2).succ := by
  induction w with
  | nil => exact (stage _).one_mem
  | cons d w ih =>
    apply Subgroup.mul_mem _ ?_ ih
    change (if d.2 then literal (nextIndex i d.1) else
      (literal (nextIndex i d.1))⁻¹) ∈ _
    split
    · exact nextIndex_mem i d.1
    · exact Subgroup.inv_mem _ (nextIndex_mem i d.1)

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.Edges

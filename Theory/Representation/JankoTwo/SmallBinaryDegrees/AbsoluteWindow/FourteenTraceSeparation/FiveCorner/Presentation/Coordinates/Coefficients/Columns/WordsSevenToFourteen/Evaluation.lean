module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Blocks

/-!
# Evaluation of the literal reverse-norm walks

A packed lookup uses its input both to choose a block and to choose the bits
within that block. `force` evaluates the intermediate point before either use.
The induction `walkNat_eq` proves that this change of evaluation order keeps
every letter of the original walk. `columnNat_eq` retains the inverse word,
the fixed cached subgroup actions, and all 25 power pairs.

This supports the finite certificates for catalogue words 7--13. Source and
conventions: `Columns/source/README.md` and `Coefficients/Arithmetic.lean`.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.WordsSevenToFourteen

-- Force a point before using it twice in a packed lookup.
def force (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | n+1 => f (n+1)
theorem force_eq (f : Nat → Nat) (n : Nat) : force f n = f n := by cases n <;> rfl

def stepNat (l : Fin 4) (x : Nat) : Nat :=
  treeLookup (if l.val % 2 == 0 then actionATree else if l.val == 1 then actionBTree else actionBInvTree) x % 24192

def walkNat (w : List (Fin 4)) (x : Nat) : Nat :=
  w.foldl (fun x l => force (stepNat l) x) x

theorem walkNat_eq (w : List (Fin 4)) (x : Point) : walkNat w x.val = (fastWalk w x).val := by
  induction w generalizing x with
  | nil => rfl
  | cons l w ih =>
    change walkNat w (force (stepNat l) x.val) = (fastWalk w (fastStep l x)).val
    rw [force_eq]
    exact ih (fastStep l x)

def columnNat (w : List (Fin 4)) (j : Fin 1008) : Nat :=
  xorList (List.ofFn fun u : Fin 5 => xorList (List.ofFn fun v : Fin 5 =>
    2 ^ (force (fun n => treeLookup labelTree n % 1008)
      (walkNat (inverseWord w) (subgroupPoint leftAction rightAction (u,v) j).val))))

theorem columnNat_eq (w : List (Fin 4)) (j : Fin 1008) :
    columnNat w j = wordColumn leftAction rightAction w j := by
  simp only [columnNat, force_eq, walkNat_eq, wordColumn, fastOrbit]

/-- The same eight-root check, with only evaluation order changed. -/
def evaluatedBlock (d : Fin 26) (q : Fin 126) : Prop :=
  ∀ r : Fin 8, columnNat (words d) (outputIndex q r) = candidate d (outputIndex q r)

theorem wordBlock_of_evaluatedBlock (d : Fin 26) (q : Fin 126)
    (h : evaluatedBlock d q) : WordBlock d q := by
  intro r
  rw [← columnNat_eq]
  exact h r

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.WordsSevenToFourteen

module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Blocks
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsZeroToSeven.Data

/-!
# Certified flat lookup for the literal word columns

Extraction of a 15-bit field commutes with extraction of its 1920-bit block.
Checking all 189 blocks therefore identifies each flat table with the original
tree at every point. The evaluator comparison retains all letters, the reversed
inverse-word convention, and every one of the 25 subgroup power pairs.

Source: Columns/source/README.md and the fixed Coefficients/Data.lean tables.
The consumer is packedColumn_eq, used by the seven WordChecks below this module.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.WordsZeroToSeven

private theorem extract_mod (a s w k : Nat) (h : s + k ≤ w) :
    ((a % 2 ^ w) >>> s) % 2 ^ k = (a >>> s) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hi : i < k
  · have his : s + i < w := by omega
    simp [hi, his]
  · simp [hi]


def packedLookup (p x : Nat) : Nat := (p >>> (15 * x)) % 32768

private theorem packedLookup_eq (p : Nat) (t : BlockTree)
    (h : ∀ q : Fin 189, (p >>> (1920 * q.val)) % 2 ^ 1920 = blockGet t q.val)
    (x : Point) : packedLookup p x.val = treeLookup t x.val := by
  unfold packedLookup treeLookup
  rw [← h ⟨x.val / 128, by have := x.isLt; omega⟩]
  change (p >>> (15 * x.val)) % 2 ^ 15 =
    (((p >>> (1920 * (x.val / 128))) % 2 ^ 1920) >>> (15 * (x.val % 128))) % 2 ^ 15
  rw [extract_mod _ _ _ _ (by omega), ← Nat.shiftRight_add]
  congr 2
  have := Nat.div_add_mod x.val 128
  omega

set_option maxRecDepth 2048 in
private theorem packed_blocks :
    (∀ q : Fin 189, (actionAPacked >>> (1920 * q.val)) % 2 ^ 1920 =
      blockGet actionATree q.val) ∧
    (∀ q : Fin 189, (actionBPacked >>> (1920 * q.val)) % 2 ^ 1920 =
      blockGet actionBTree q.val) ∧
    (∀ q : Fin 189, (actionBInvPacked >>> (1920 * q.val)) % 2 ^ 1920 =
      blockGet actionBInvTree q.val) ∧
    (∀ q : Fin 189, (labelPacked >>> (1920 * q.val)) % 2 ^ 1920 =
      blockGet labelTree q.val) ∧
    (∀ q : Fin 189, (leftPacked >>> (1920 * q.val)) % 2 ^ 1920 =
      blockGet leftTree q.val) ∧
    (∀ q : Fin 189, (rightPacked >>> (1920 * q.val)) % 2 ^ 1920 =
      blockGet rightTree q.val) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def packedStep (l : Fin 4) (x : Point) : Point :=
  ⟨packedLookup (if l.val % 2 == 0 then actionAPacked else
    if l.val == 1 then actionBPacked else actionBInvPacked) x.val % 24192,
    Nat.mod_lt _ (by decide)⟩
def packedWalk (w : List (Fin 4)) (x : Point) : Point :=
  w.foldl (fun x l => packedStep l x) x

def packedLeft (x : Point) : Point :=
  ⟨packedLookup leftPacked x.val % 24192, Nat.mod_lt _ (by decide)⟩
def packedRight (x : Point) : Point :=
  ⟨packedLookup rightPacked x.val % 24192, Nat.mod_lt _ (by decide)⟩
def packedOrbit (x : Point) : Fin 1008 :=
  ⟨packedLookup labelPacked x.val % 1008, Nat.mod_lt _ (by decide)⟩

theorem packedStep_eq : packedStep = fastStep := by
  funext l x
  apply Fin.ext
  fin_cases l
  · exact congrArg (· % 24192) (packedLookup_eq _ _ packed_blocks.1 x)
  · exact congrArg (· % 24192) (packedLookup_eq _ _ packed_blocks.2.1 x)
  · exact congrArg (· % 24192) (packedLookup_eq _ _ packed_blocks.1 x)
  · exact congrArg (· % 24192) (packedLookup_eq _ _ packed_blocks.2.2.1 x)

theorem packedWalk_eq (w : List (Fin 4)) (x : Point) :
    packedWalk w x = fastWalk w x := by
  simp only [packedWalk, packedStep_eq, fastWalk]

theorem packedLeft_eq : packedLeft = leftAction := by
  funext x
  apply Fin.ext
  exact congrArg (· % 24192) (packedLookup_eq _ _ packed_blocks.2.2.2.2.1 x)

theorem packedRight_eq : packedRight = rightAction := by
  funext x
  apply Fin.ext
  exact congrArg (· % 24192) (packedLookup_eq _ _ packed_blocks.2.2.2.2.2 x)

theorem packedOrbit_eq (x : Point) : packedOrbit x = fastOrbit x := by
  apply Fin.ext
  exact congrArg (· % 1008) (packedLookup_eq _ _ packed_blocks.2.2.2.1 x)

/-- The same literal inverse word and all 25 original power pairs. -/
def packedColumn (w : List (Fin 4)) (j : Fin 1008) : Nat :=
  xorList (List.ofFn fun u : Fin 5 => xorList (List.ofFn fun v : Fin 5 =>
    2 ^ (packedOrbit (packedWalk (inverseWord w)
      (subgroupPoint packedLeft packedRight (u,v) j))).val))

/-- Pointwise comparison with the actual consumer's original word column. -/
theorem packedColumn_eq (w : List (Fin 4)) (j : Fin 1008) :
    packedColumn w j = wordColumn leftAction rightAction w j := by
  simp only [packedColumn, packedWalk_eq, packedOrbit_eq,
    packedLeft_eq, packedRight_eq, wordColumn]

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.WordsZeroToSeven

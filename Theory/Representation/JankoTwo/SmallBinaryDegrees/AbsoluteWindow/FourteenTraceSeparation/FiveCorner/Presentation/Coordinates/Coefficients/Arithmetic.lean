module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Model
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Action
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Packed reverse-norm coefficient columns

A singleton bit records the input orbit reached from an output root. XOR adds
these indicators in F₂. The two nested five-element lists retain all 25 terms,
even when several subgroup elements reach the same point. The outer word list
retains all multiplicities in the nine literal generators. Only those generator
words are inverted; the cached subgroup action is applied in its original order.

`columnFromRows` reads one bit of each existing row in a single list traversal.
The two remaining numerical obligations are the correctness of the cached
subgroup actions and equality of these packed columns. Coefficients.lean
connects them to the exact original CoefficientCertificate.

Source: Coordinates/source/README.md and its reverse-norm convention.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients

def bit (n i : Nat) : ZMod 2 := if n.testBit i then 1 else 0
lemma bit_xor (m n i : Nat) : bit (m ^^^ n) i = bit m i + bit n i := by
  simp only [bit, Nat.testBit_xor]
  cases m.testBit i <;> cases n.testBit i <;> decide
lemma bit_zero (i : Nat) : bit 0 i = 0 := by simp [bit]
lemma bit_single (i j : Nat) : bit (2 ^ i) j = if i = j then 1 else 0 := by
  simp [bit, Nat.testBit_two_pow]
def xorList : List Nat → Nat
  | [] => 0
  | x :: xs => x ^^^ xorList xs
lemma bit_xorList (xs : List Nat) (i : Nat) :
    bit (xorList xs) i = (xs.map (fun x => bit x i)).sum := by
  induction xs with
  | nil => exact bit_zero _
  | cons x xs ih => simp only [xorList, bit_xor, ih, List.map_cons, List.sum_cons]
lemma bit_xor_ofFn {n : Nat} (f : Fin n → Nat) (i : Nat) :
    bit (xorList (List.ofFn f)) i = ∑ j, bit (f j) i := by
  simp only [bit_xorList, List.map_ofFn, List.sum_ofFn, Function.comp_apply]

def iteratePoint (f : Point → Point) : Nat → Point → Point
  | 0, x => x
  | n+1, x => iteratePoint f n (f x)
lemma iteratePoint_walk (w : List (Fin 4)) (n : Nat) (x : Point) :
    iteratePoint (walk w) n x = walk (List.replicate n w).flatten x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [iteratePoint, List.replicate_succ, List.flatten_cons, walk, List.foldl_append] at *
    exact ih _

def subgroupPoint (L R : Point → Point) (t : CoefficientTheory.PowerIndex)
    (j : Fin 1008) : Point := iteratePoint R t.2.val (iteratePoint L t.1.val (root j))
lemma subgroupPoint_eq (L R : Point → Point) (hL : L = walk leftWord)
    (hR : R = walk rightWord) (t : CoefficientTheory.PowerIndex) (j : Fin 1008) :
    subgroupPoint L R t j = walk (subgroupWord t) (root j) := by
  subst L; subst R
  simp only [subgroupPoint, iteratePoint_walk, subgroupWord, walk, List.foldl_append]

def wordColumn (L R : Point → Point) (w : List (Fin 4)) (j : Fin 1008) : Nat :=
  xorList (List.ofFn fun u : Fin 5 => xorList (List.ofFn fun v : Fin 5 =>
    2 ^ (fastOrbit (fastWalk (inverseWord w) (subgroupPoint L R (u,v) j))).val))
lemma bit_wordColumn (L R : Point → Point) (hL : L = walk leftWord)
    (hR : R = walk rightWord) (w : List (Fin 4)) (i j : Fin 1008) :
    bit (wordColumn L R w j) i.val = wordEntry w i j := by
  simp only [wordColumn, fastWalk_eq, fastOrbit_eq, bit_xor_ofFn, bit_single, subgroupPoint_eq L R hL hR,
    wordEntry, CoefficientTheory.PowerIndex, Fintype.sum_prod_type, Fin.ext_iff]

def column (L R : Point → Point) (k : Fin 9) (j : Fin 1008) : Nat :=
  xorList ((generatorWords k).map fun w => wordColumn L R w j)
lemma bit_column (L R : Point → Point) (hL : L = walk leftWord)
    (hR : R = walk rightWord) (k : Fin 9) (i j : Fin 1008) :
    bit (column L R k j) i.val = countEntry k i j := by
  simp only [column, bit_xorList, List.map_map, Function.comp_def,
    bit_wordColumn L R hL hR, countEntry]

def columnFromRows (j : Nat) : List Nat → Nat
  | [] => 0
  | r :: rs => (if r.testBit j then 1 else 0) ||| (columnFromRows j rs <<< 1)

lemma testBit_columnFromRows (rs : List Nat) (i j : Nat) :
    (columnFromRows j rs).testBit i = (rs[i]!).testBit j := by
  induction rs generalizing i with
  | nil => simp [columnFromRows]
  | cons r rs ih =>
    cases i with
    | zero => cases h : r.testBit j <;> simp [columnFromRows, h]
    | succ i =>
      have h1 : (1 : Nat).testBit (i + 1) = false := by simp [Nat.testBit_add_one]
      simp only [columnFromRows, Nat.testBit_or, Nat.testBit_shiftLeft,
        List.getElem!_cons_succ, Nat.add_one_sub_one, ih]
      cases r.testBit j <;> simp [h1]

/-- Numerical column checks using the fixed candidate subgroup cache. -/
def ColumnChecks : Prop :=
  ∀ (k : Fin 9) (j : Fin 1008),
    column leftAction rightAction k j = columnFromRows j.val (rows k).toList

lemma bit_columnFromRows (k : Fin 9) (i j : Fin 1008) :
    bit (columnFromRows j.val (rows k).toList) i.val = entry k i j := by
  simp only [bit, testBit_columnFromRows, Array.getElem!_toList, entry]

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients

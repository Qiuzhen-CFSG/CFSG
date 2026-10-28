module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Data
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Algebra
import Mathlib.Tactic.FinCases

/-!
# The fixed finite model and its two independent certificates

The action tables and representative words are decoded from packed natural
numbers. `RightCosetGeometry` identifies them with the actual right cosets of
the literal order-25 subgroup and gives double-coset coverage. The independent
`CoefficientCertificate` compares reverse-norm counts with the existing nine
operator arrays. Neither certificate is asserted here.

The reverse-norm counts use all 25 power pairs, with the generator word
inverted and read backwards. Coordinates.lean proves that these two inputs
suffice for faithful coordinates on the actual corner. This avoids both a
normality assumption and a full group-algebra multiplication table.

Source and conventions: Presentation/source/README.md and Coordinates/source/README.md;
local application: Guralnick--Malle Proposition 5.1.
-/

@[expose] public section

namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation
open Sporadic.LeechRelated.J2
namespace OrbitData

abbrev Point := Fin 24192

/-- Fixed-width little-endian entries, 128 entries per natural-number block. -/
def lookup (width : ℕ) (a : Array ℕ) (n : ℕ) : ℕ :=
  (a[n / 128]! >>> (width * (n % 128))) % 2 ^ width

def step (l : Fin 4) (x : Point) : Point :=
  ⟨(lookup 15 (![actionA, actionB, actionA, actionBInv] l) x.val) % 24192,
    Nat.mod_lt _ (by decide)⟩

def walk (w : List (Fin 4)) (x : Point) : Point :=
  w.foldl (fun x l => step l x) x

def orbit (x : Point) : Fin 1008 :=
  ⟨(lookup 15 orbitLabels x.val) % 1008, Nat.mod_lt _ (by decide)⟩

def root (i : Fin 1008) : Point :=
  ⟨(lookup 15 orbitRoots i.val) % 24192, Nat.mod_lt _ (by decide)⟩

/-- Decode the exact saved BFS word, with the first letter in the lowest two bits. -/
def representativeWord (i : Fin 1008) : List (Fin 4) :=
  (List.range (lookup 6 representativeLengths i.val)).map fun j =>
    ⟨(lookup 80 representativeCodes i.val >>> (2 * j)) % 4, Nat.mod_lt _ (by decide)⟩

def representative (i : Fin 1008) : Carrier := word (representativeWord i)

def inverseLetter : Fin 4 → Fin 4 := ![2, 3, 0, 1]

def inverseWord (w : List (Fin 4)) : List (Fin 4) :=
  w.reverse.map inverseLetter

def subgroupWord (t : CoefficientTheory.PowerIndex) : List (Fin 4) :=
  (List.replicate t.1.val leftWord).flatten ++
    (List.replicate t.2.val rightWord).flatten

theorem letter_inverseLetter (l : Fin 4) : letter (inverseLetter l) = (letter l)⁻¹ := by
  fin_cases l <;> simp [inverseLetter, letter]

theorem word_append (u v : List (Fin 4)) : word (u ++ v) = word u * word v := by
  simp [word]

theorem word_inverseWord (w : List (Fin 4)) : word (inverseWord w) = (word w)⁻¹ := by
  induction w with
  | nil => simp [inverseWord, word]
  | cons l w ih =>
    simp only [inverseWord, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      word_append] at *
    simpa [word, letter_inverseLetter] using congrArg (· * (letter l)⁻¹) ih

theorem word_subgroupWord (t : CoefficientTheory.PowerIndex) :
    word (subgroupWord t) = (CoefficientTheory.subgroupElement t : Carrier) := by
  have hrep (w : List (Fin 4)) (n : ℕ) :
      word (List.replicate n w).flatten = word w ^ n := by
    induction n with
    | zero => simp [word]
    | succ n ih => simp [List.replicate_succ, word_append, ih, pow_succ']
  simp only [subgroupWord, word_append, hrep, CoefficientTheory.subgroupElement,
    leftGenerator, rightGenerator]

set_option maxRecDepth 10000 in
theorem root_eq_zero_iff (i : Fin 1008) : root i = 0 ↔ i = 0 := by
  revert i
  decide +kernel

/-- The reverse-norm coefficient, input orbit i and output orbit j.
The inverse belongs only to the generator word. The sum traverses all 25
subgroup elements, so inversion of that summation variable is unnecessary. -/
def wordEntry (w : List (Fin 4)) (i j : Fin 1008) : ZMod 2 :=
  ∑ t : CoefficientTheory.PowerIndex,
    if orbit (walk (inverseWord w) (walk (subgroupWord t) (root j))) = i
      then (1 : ZMod 2) else 0

/-- Sum the literal condensed-word coefficients in one of the nine generators. -/
def countEntry (k : Fin 9) (i j : Fin 1008) : ZMod 2 :=
  ((generatorWords k).map fun w => wordEntry w i j).sum

/-- Independent finite arithmetic obligation on the fixed action arrays. -/
def CoefficientCertificate : Prop :=
  ∀ k i j, countEntry k i j = entry k i j

/-- Geometric certificate for the fixed arrays. The equality criterion uses
right cosets P\\G: c(g)=c(h) iff h*g⁻¹ lies in P. No normality is assumed.
The final field states double-coset coverage with exactly the saved orbit label;
it is to be proved from the actual action and the saved orbit witnesses. -/
structure RightCosetGeometry where
  coset : Carrier → Point
  coset_one : coset 1 = 0
  coset_eq_iff : ∀ g h, coset g = coset h ↔ h * g⁻¹ ∈ subgroup
  coset_letter : ∀ g l, coset (g * letter l) = step l (coset g)
  coset_representative : ∀ i, coset (representative i) = root i
  double_cover : ∀ g, ∃ p q : subgroup,
    g = (p : Carrier) * representative (orbit (coset g)) * (q : Carrier)

namespace RightCosetGeometry

/-- The saved action must realize the actual right-coset setoid. -/
theorem coset_eq_iff_rightRel (C : RightCosetGeometry) (g h : Carrier) :
    C.coset g = C.coset h ↔ QuotientGroup.rightRel subgroup g h := by
  rw [C.coset_eq_iff, QuotientGroup.rightRel_apply]

theorem coset_word (C : RightCosetGeometry) (g : Carrier) (w : List (Fin 4)) :
    C.coset (g * word w) = walk w (C.coset g) := by
  induction w generalizing g with
  | nil => simp [word, walk]
  | cons l w ih =>
    simpa [word, walk, List.foldl_cons, ← mul_assoc, C.coset_letter] using
      ih (g * letter l)

theorem representative_mem_iff (C : RightCosetGeometry) (i : Fin 1008) :
    representative i ∈ subgroup ↔ i = 0 := by
  have h := C.coset_eq_iff 1 (representative i)
  calc
    representative i ∈ subgroup ↔ 0 = root i := by
      simpa only [C.coset_one, C.coset_representative, inv_one, mul_one] using h.symm
    _ ↔ root i = 0 := eq_comm
    _ ↔ i = 0 := root_eq_zero_iff i

end RightCosetGeometry
end OrbitData
end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation

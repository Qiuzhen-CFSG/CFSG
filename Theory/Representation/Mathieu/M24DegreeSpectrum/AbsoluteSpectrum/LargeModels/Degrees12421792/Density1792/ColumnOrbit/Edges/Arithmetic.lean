module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Arithmetic
/-!
# Soundness of sequential column-edge computations

A packed row of the transpose is a column of the original matrix. Selecting
these rows by a packed input vector and taking their XOR is therefore the
original left matrix action. `mulVec_of_select` proves that interpretation;
`transpose_of_checked` verifies every transpose entry by a sequential scan.
Arithmetic bit tests use division by powers of two to avoid linear shift
reduction. Concrete consumers and the remaining numeric obligations are in
`Edges.lean` and `Edges/Contracts.lean`.

Source: the literal ATLAS M24G1-f2r1792B0 matrices; attribution and conventions
in `source/README.md`. No externally computed equality is trusted here.
-/

@[expose] public section
open Thompson.BinaryMatrix Matrix
open scoped BigOperators
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges

def fastBit (x i : Nat) : Bool := x / 2^i % 2 == 1

theorem fastBit_eq (x i : Nat) : fastBit x i = x.testBit i := by
  apply Bool.eq_iff_iff.mpr
  simp [fastBit, Nat.testBit_eq_decide_div_mod_eq]

def select : List Nat → Nat → Nat
 | [], _ => 0
 | _::_, 0 => 0
 | r::rs, x+1 => (if (x+1)%2 == 1 then r else 0) ^^^ select rs ((x+1)/2)

theorem select_zero (rs : List Nat) : select rs 0 = 0 := by cases rs <;> rfl

theorem select_cons (r : Nat) (rs : List Nat) (x : Nat) :
    select (r::rs) x = (if fastBit x 0 then r else 0) ^^^ select rs (x/2) := by
  cases x <;> simp [select, fastBit, select_zero]

theorem bit_select (rs : List Nat) (x j : Nat) :
    bit (select rs x) j = ∑ i : Fin rs.length, bit x i.val * bit rs[i.val] j := by
  induction rs generalizing x with
  | nil => simp [select, bit]
  | cons r rs ih =>
    simp only [List.length_cons]
    rw [select_cons, bit_xor, Fin.sum_univ_succ, ih]
    simp only [Fin.val_zero, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ]
    congr 1
    · rw [fastBit_eq]
      cases h : x.testBit 0 <;> simp [bit, h]
    · apply Finset.sum_congr rfl
      intro i _
      simp only [bit, Nat.testBit_div_two]

def matrix (n : Nat) (rs : List Nat) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => bit rs[i.val]! j.val

theorem vector_select (n : Nat) (rs : List Nat) (h : rs.length = n) (x : Nat) :
    ColumnCertificate.vector n (select rs x) = vecMul (ColumnCertificate.vector n x) (matrix n rs) := by
  subst n
  funext j
  rw [ColumnCertificate.vector, bit_select]
  apply Finset.sum_congr rfl
  intro i _
  simp only [matrix, ColumnCertificate.vector, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem i.isLt, Option.getD_some]

/-- Verify one candidate transpose row by sequentially reading the original rows. -/
def checkTransposeRow (j t : Nat) : List Nat → Nat → Bool
 | [], _ => true
 | r::rs, c => (fastBit r j == fastBit t c) && checkTransposeRow j t rs (c+1)

theorem checkTransposeRow_sound (j t : Nat) (rs : List Nat) (c : Nat)
    (h : checkTransposeRow j t rs c = true) (i : Nat) (hi : i < rs.length) :
    rs[i]!.testBit j = t.testBit (c+i) := by
  induction rs generalizing c i with
  | nil => simp at hi
  | cons r rs ih =>
    simp only [checkTransposeRow, Bool.and_eq_true, beq_iff_eq, fastBit_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have ht := ih (c+1) h.2 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht

theorem transpose_of_checked (n : Nat) (rs : Array Nat) (ts : List Nat)
    (hlen : rs.size = n)
    (h : ∀ j : Fin n, checkTransposeRow j.val ts[j.val]! rs.toList 0 = true) :
    matrix n ts = (decode n rs).transpose := by
  funext j i
  have hb := checkTransposeRow_sound j.val ts[j.val]! rs.toList 0 (h j) i.val
    (by simp [hlen])
  simp only [Nat.zero_add, Array.getElem!_toList] at hb
  simp only [matrix, transpose_apply, decode, bit, hb]

theorem mulVec_of_select (n : Nat) (rs : Array Nat) (ts : List Nat)
    (ht : matrix n ts = (decode n rs).transpose) (hlen : ts.length = n)
    (x y : Nat) (h : select ts x = y) :
    (decode n rs).mulVec (ColumnCertificate.vector n x) = ColumnCertificate.vector n y := by
  have hv := vector_select n ts hlen x
  rw [h, ht, vecMul_transpose] at hv
  exact hv.symm

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges

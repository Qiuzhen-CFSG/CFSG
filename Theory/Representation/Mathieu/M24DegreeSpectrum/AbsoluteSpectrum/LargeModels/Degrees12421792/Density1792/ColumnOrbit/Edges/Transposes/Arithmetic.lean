module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.Data

/-!
# Entrywise verification of blocked transpose tables

A rectangle is checked by packing each original column and comparing it with
an aligned slice of the candidate transpose. The binary place of every block
is checked independently. The soundness proofs identify each bit, concatenate
adjacent row blocks, and recover the transpose of the original decoded array.
Small blocks avoid repeatedly reducing a long indexed array or divisor chain.
The concrete applications are `ColumnEdges.firstTranspose_eq` and
`ColumnEdges.secondTranspose_eq` in the parent module.

Source: the literal ATLAS M24G1-f2r1792B0 matrices; see `source/README.md` and
`../source/README.md` for attribution and the original row/column convention.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges.Transposes

/-- Read one column of a row list, using a fixed binary place divisor. -/
def packedColumn (p : Nat) : List Nat → Nat
  | [] => 0
  | r :: rs => r / p % 2 + 2 * packedColumn p rs

theorem packedColumn_bit (j : Nat) (rs : List Nat) (i : Nat) (hi : i < rs.length) :
    (packedColumn (2^j) rs).testBit i = rs[i]!.testBit j := by
  induction rs generalizing i with
  | nil => simp at hi
  | cons r rs ih =>
    simp only [packedColumn]
    rw [Nat.add_comm, show 2 * packedColumn (2^j) rs =
      2^1 * packedColumn (2^j) rs by rfl,
      Nat.testBit_two_pow_mul_add _ (by simpa using Nat.mod_lt (r / 2^j) (by decide : 0 < 2))]
    cases i with
    | zero =>
      simp [Nat.testBit_eq_decide_div_mod_eq]
    | succ i =>
      simpa using ih i (by simpa using hi)

/-- Check a rectangle against the corresponding binary slices of its columns. -/
def checkTile (rs : List Nat) (q : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | t :: ts, p => (packedColumn p rs == (t / q % 2^rs.length)) &&
      checkTile rs q ts (p * 2)

theorem checkTile_append (rs as bs : List Nat) (q p : Nat) :
    checkTile rs q (as ++ bs) p =
      (checkTile rs q as p && checkTile rs q bs (p * 2^as.length)) := by
  induction as generalizing p with
  | nil => simp [checkTile]
  | cons a as ih =>
    simp only [List.cons_append, checkTile, ih, List.length_cons]
    simp [Bool.and_assoc, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]

theorem checkTile_sound (rs ts : List Nat) (q p : Nat)
    (h : checkTile rs q ts p = true) (i : Nat) (hi : i < ts.length) :
    packedColumn (p * 2^i) rs = ts[i]! / q % 2^rs.length := by
  induction ts generalizing p i with
  | nil => simp at hi
  | cons t ts ih =>
    simp only [checkTile, Bool.and_eq_true, beq_iff_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have ht := ih (p * 2) h.2 i (by simpa using hi)
      simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using ht

/-- Blocks carry their binary divisors; checking these separately prevents
repeated evaluation of a long chain of powers in every rectangle. -/
abbrev Blocks := List (Nat × List Nat)

def flatten (bs : Blocks) : List Nat := bs.flatMap Prod.snd

def checkDivisors : Blocks → Nat → Bool
  | [], _ => true
  | (p, ts) :: bs, start => (p == start) && checkDivisors bs (p * 2^ts.length)

def checkRow (rs : List Nat) (q : Nat) : Blocks → Bool
  | [] => true
  | (p, ts) :: bs => checkTile rs q ts p && checkRow rs q bs

theorem checkRow_sound (rs : List Nat) (q : Nat) (bs : Blocks) (p : Nat)
    (hp : checkDivisors bs p = true) (h : checkRow rs q bs = true) :
    checkTile rs q (flatten bs) p = true := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih =>
    rcases b with ⟨p', ts⟩
    simp only [checkDivisors, Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨he, hp⟩ := hp
    subst p'
    simp only [checkRow, Bool.and_eq_true] at h
    simp only [flatten, List.flatMap_cons, checkTile_append, Bool.and_eq_true]
    exact ⟨h.1, ih _ hp h.2⟩

/-- Every entry of a consecutive group of original rows agrees with the columns. -/
def Agrees (rs ts : List Nat) (r : Nat) : Prop :=
  ∀ i : Nat, i < rs.length → ∀ j : Nat, j < ts.length →
    rs[i]!.testBit j = ts[j]!.testBit (r + i)

theorem agrees_of_checkRow (rs : List Nat) (ts : Blocks) (r : Nat)
    (ht : checkDivisors ts 1 = true)
    (h : checkRow rs (2^r) ts = true) : Agrees rs (flatten ts) r := by
  intro i hi j hj
  have h' := checkRow_sound rs (2^r) ts 1 ht h
  have hc := checkTile_sound rs (flatten ts) (2^r) 1 h' j hj
  simp only [Nat.one_mul] at hc
  have hb := packedColumn_bit j rs i hi
  rw [hc] at hb
  simpa [Nat.testBit_div_two_pow, hi, Nat.add_comm] using hb.symm

theorem agrees_append (as bs ts : List Nat) (r : Nat)
    (ha : Agrees as ts r) (hb : Agrees bs ts (r + as.length)) :
    Agrees (as ++ bs) ts r := by
  intro i hi j hj
  by_cases hia : i < as.length
  · simpa only [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hia]
      using ha i hia j hj
  · have hle : as.length ≤ i := by omega
    have hib : i - as.length < bs.length := by simp only [List.length_append] at hi; omega
    have he : r + as.length + (i - as.length) = r + i := by omega
    simpa only [List.getElem!_eq_getElem?_getD, List.getElem?_append_right hle, he]
      using hb (i - as.length) hib j hj

def checkGrid (ts : Blocks) : Blocks → Bool
  | [] => true
  | (q, rs) :: bs => checkRow rs q ts && checkGrid ts bs

theorem agrees_of_checkGrid (rs ts : Blocks) (r : Nat)
    (hr : checkDivisors rs (2^r) = true) (ht : checkDivisors ts 1 = true)
    (h : checkGrid ts rs = true) : Agrees (flatten rs) (flatten ts) r := by
  induction rs generalizing r with
  | nil => intro i hi; simp [flatten] at hi
  | cons b bs ih =>
    rcases b with ⟨q, rs⟩
    simp only [checkDivisors, Bool.and_eq_true, beq_iff_eq] at hr
    obtain ⟨he, hr⟩ := hr
    subst q
    simp only [checkGrid, Bool.and_eq_true] at h
    apply agrees_append _ _ _ r (agrees_of_checkRow rs ts r ht h.1)
    apply ih (r + rs.length) _ h.2
    simpa only [Nat.pow_add] using hr

open Thompson.BinaryMatrix Matrix in
theorem transpose_of_grid (n : Nat) (a : Array Nat) (b : List Nat)
    (rs ts : Blocks) (hr : flatten rs = a.toList) (ht : flatten ts = b)
    (ha : a.size = n) (hb : b.length = n)
    (hdr : checkDivisors rs 1 = true) (hdt : checkDivisors ts 1 = true)
    (h : checkGrid ts rs = true) :
    matrix n b = (decode n a).transpose := by
  have hg := agrees_of_checkGrid rs ts 0 hdr hdt h
  rw [hr, ht] at hg
  funext j i
  have he := hg i.val (by simp [ha]) j.val (by simp [hb])
  simp only [Nat.zero_add, Array.getElem!_toList] at he
  simp only [matrix, transpose_apply, decode, bit, he]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges.Transposes

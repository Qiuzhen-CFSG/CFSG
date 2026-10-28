module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic

/-!
# Fast, checked multiplication for the literal degree-1792 generators

Balanced radix conversion skips zero blocks; a proved monomial branch selects
one row directly. Both branches have the same binary matrix semantics. The
carry-free product theorem from Arithmetic discharges the dense branch.
Every table and hint remains untrusted data until the kernel checks its use.

Source: ATLAS M24G1-P1 and M24G1-f2r1792B0.m1/.m2; see
`../../../source/README.md` and `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic

theorem expand_zero (n : Nat) : expand n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [expand, ih]

theorem expand_mod (n a : Nat) : expand n (a % 2^n) = expand n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [expand, pow_succ']
    rw [Nat.mod_mul_right_div_self, ih, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 (2^n))]

def expandTree : Nat → Nat → Nat → Nat
  | 0, n, a => expand n a
  | k+1, n, a => if a == 0 then 0 else
      let m := n / 2
      expandTree k m (a % 2^m) + 2048^m * expandTree k (n-m) (a / 2^m)

theorem expandTree_eq (k n a : Nat) : expandTree k n a = expand n a := by
  induction k generalizing n a with
  | zero => rfl
  | succ k ih =>
    simp only [expandTree]
    split
    · next h =>
        have ha : a = 0 := by simpa only [beq_iff_eq] using h
        rw [ha, expand_zero]
    · rw [ih, ih, expand_mod, ← expand_add]
      congr 1
      omega

theorem compress_zero (n : Nat) : compress n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [compress, ih]

theorem compress_mod (n a : Nat) : compress n (a % 2048^n) = compress n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [compress, pow_succ']
    rw [Nat.mod_mul_right_div_self, ih,
      Nat.mod_mod_of_dvd _ (dvd_mul_of_dvd_left (by decide : 2 ∣ 2048) _)]

def compressTree : Nat → Nat → Nat → Nat
  | 0, n, a => compress n a
  | k+1, n, a => if a == 0 then 0 else
      let m := n / 2
      compressTree k m (a % 2048^m) + 2^m * compressTree k (n-m) (a / 2048^m)

theorem compressTree_eq (k n a : Nat) : compressTree k n a = compress n a := by
  induction k generalizing n a with
  | zero => rfl
  | succ k ih =>
    simp only [compressTree]
    split
    · next h =>
        have ha : a = 0 := by simpa only [beq_iff_eq] using h
        rw [ha, compress_zero]
    · rw [ih, ih, compress_mod, ← compress_add]
      congr 1
      omega

open scoped BigOperators
open Thompson.BinaryMatrix

def getRow (width : Nat) (rows : List (List Nat)) (i : Nat) : Nat :=
  (rows[i / width]!)[i % width]!

theorem getRow_eq (width : Nat) (hw : 0 < width) (rows : List (List Nat))
    (hr : ∀ r ∈ rows, r.length = width) (i : Nat) :
    getRow width rows i = rows.flatten[i]! := by
  induction rows generalizing i with
  | nil => simp [getRow]; rfl
  | cons r rs ih =>
    have hl : r.length = width := hr r (by simp)
    have ht : ∀ t ∈ rs, t.length = width := fun t h => hr t (by simp [h])
    by_cases hi : i < width
    · simp [getRow, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi,
        List.getElem!_eq_getElem?_getD, List.getElem?_append, hl, hi]
    · have hi' : width ≤ i := by omega
      rw [getRow, Nat.div_eq_sub_div hw hi', Nat.mod_eq_sub_mod hi']
      simpa [getRow, List.getElem!_eq_getElem?_getD, List.getElem?_append,
        hl, hi, Nat.add_comm] using ih ht (i-width)

def rowFast (n width : Nat) (rows wide : List (List Nat)) (x : Nat × Nat) : Nat :=
  if x.1 = 2^x.2 ∧ x.2 < n then getRow width rows x.2
  else compressTree 6 n (accumChunks x.1 wide)

theorem bit_rowFast (n width : Nat) (hn : n < 2048) (hw : 0 < width)
    (rows wide : List (List Nat))
    (hr : ∀ r ∈ rows, r.length = width) (hy : rows.flatten.length = n)
    (he : wide.flatten = rows.flatten.map (expand n)) (x : Nat × Nat) (j : Fin n) :
    bit (rowFast n width rows wide x) j.val =
      ∑ k : Fin n, bit x.1 k.val * bit rows.flatten[k.val]! j.val := by
  unfold rowFast
  split
  · next h =>
      rw [getRow_eq width hw rows hr, h.1]
      have hb (k : Fin n) : bit (2^x.2) k.val =
          if k = (⟨x.2, h.2⟩ : Fin n) then 1 else 0 := by
        simp [bit, Nat.testBit_two_pow, Fin.ext_iff, eq_comm]
      simp_rw [hb]
      simp
  · rw [compressTree_eq, accumChunks_eq]
    have hl : wide.flatten = List.ofFn (fun k : Fin n => expand n rows.flatten[k.val]!) := by
      subst n
      rw [he]
      simpa only [List.map_ofFn, Function.comp_def] using
        congrArg (List.map (expand rows.flatten.length)) (ofFn_get! rows.flatten).symm
    rw [hl]
    exact bit_product n x.1 hn (fun k => rows.flatten[k.val]!) j

theorem product_fast (n width : Nat) (hn : n < 2048) (hw : 0 < width)
    (rows wide : List (List Nat)) (xs : List (Nat × Nat)) (zs : List Nat)
    (hr : ∀ r ∈ rows, r.length = width) (hy : rows.flatten.length = n)
    (he : wide.flatten = rows.flatten.map (expand n)) (hx : xs.length = n)
    (hc : xs.map (rowFast n width rows wide) = zs) :
    decodeRows n (xs.map Prod.fst) * decodeRows n rows.flatten = decodeRows n zs := by
  ext i j
  have hxi : i.val < xs.length := by simpa only [hx] using i.isLt
  have hzi : i.val < zs.length := by rw [← hc, List.length_map]; exact hxi
  have hi := congrArg (fun l : List Nat => l[i.val]?) hc
  have hi' : rowFast n width rows wide xs[i.val] = zs[i.val] := by
    simpa [List.getElem?_map, hxi, hzi] using hi
  change (∑ k : Fin n, bit (xs.map Prod.fst)[i.val]! k.val *
    bit rows.flatten[k.val]! j.val) = bit zs[i.val]! j.val
  have hi'' : (xs.map Prod.fst)[i.val]! = xs[i.val].1 := by simp [hxi]
  rw [hi'']
  rw [← bit_rowFast n width hn hw rows wide hr hy he xs[i.val] j, hi']
  simp [hzi]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders

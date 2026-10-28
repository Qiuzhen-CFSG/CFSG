module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.List.Indexes

/-!
# Carry-free binary matrix certificates in degree below 2048

A binary row is expanded to base 2048. Adding at most 2047 selected rows cannot
carry between columns. Taking each digit modulo two therefore computes the
ordinary product over `ZMod 2`. The expansion, accumulation, and compression
are proved correct; literal data and closed checks remain untrusted inputs.

Blocked traversals bound the recursive reductions in the concrete certificates.
The digit argument follows the project's
`ONan/ProjectiveOrder/CosetIndex/UpperBound/Packed/Arithmetic.lean` and
`Lyons/Atlas111LocalRelationArithmetic.lean`, adapted to the literal binary
row convention. The intended consumer is the ATLAS M24 degree-1792 pair:
see `../../source/README.md` and `../source/README.md`.
-/

@[expose] public section
open scoped BigOperators
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
open Thompson.BinaryMatrix

def pack (radix : Nat) {n : Nat} (f : Fin n → Nat) : Nat :=
  Nat.ofDigits radix (List.ofFn f)
def digit (radix a j : Nat) : Nat := a / radix ^ j % radix

theorem digit_pack (radix : Nat) (hr : 0 < radix) {n : Nat}
    (f : Fin n → Nat) (hf : ∀ j, f j < radix) (j : Fin n) :
    digit radix (pack radix f) j.val = f j := by
  unfold digit pack
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop]
  · rw [Nat.ofDigits_mod_eq_head!]
    simp [List.head!_eq_head?_getD, Nat.mod_eq_of_lt (hf j)]
  · exact hr
  · simpa using hf

theorem pack_sum (radix : Nat) {n m : Nat} (f : Fin m → Fin n → Nat) :
    pack radix (fun j => ∑ k, f k j) = ∑ k, pack radix (f k) := by
  simp only [pack, Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn,
    List.length_ofFn, List.get_ofFn, List.sum_ofFn, Finset.sum_mul]
  exact Finset.sum_comm

theorem pack_mul (radix : Nat) {n : Nat} (c : Nat) (f : Fin n → Nat) :
    pack radix (fun j => c * f j) = c * pack radix f := by
  simp only [pack, Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn,
    List.length_ofFn, List.get_ofFn, List.sum_ofFn, Finset.mul_sum, mul_assoc]
  rfl

def expand : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, x => x % 2 + 2048 * expand n (x / 2)

def compress : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, x => x % 2 + 2 * compress n (x / 2048)

def accum : Nat → List Nat → Nat
  | _, [] => 0
  | a, b :: bs => (a % 2) * b + accum (a / 2) bs

theorem digit_two_div (a j : Nat) : digit 2 (a / 2) j = digit 2 a (j+1) := by
  simp [digit, pow_succ', Nat.div_div_eq_div_mul]

theorem expand_eq (n a : Nat) :
    expand n a = pack 2048 (fun j : Fin n => digit 2 a j.val) := by
  induction n generalizing a with
  | zero => simp [expand, pack]
  | succ n ih =>
    simp [expand, pack, List.ofFn_succ, Nat.ofDigits_cons, ih, digit, pow_succ', Nat.div_div_eq_div_mul]

theorem compress_eq (n a : Nat) :
    compress n a = pack 2 (fun j : Fin n => digit 2048 a j.val % 2) := by
  induction n generalizing a with
  | zero => simp [compress, pack]
  | succ n ih =>
    simp [compress, pack, List.ofFn_succ, Nat.ofDigits_cons, ih, digit, pow_succ', Nat.div_div_eq_div_mul]

theorem bit_eq_digit (a j : Nat) : bit a j = (digit 2 a j : ZMod 2) := by
  unfold bit digit
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h := Nat.mod_lt (a / 2 ^ j) (by decide : 0 < 2)
  interval_cases (a / 2 ^ j % 2) <;> rfl

theorem bit_compress (n a : Nat) (j : Fin n) :
    bit (compress n a) j.val = (digit 2048 a j.val : ZMod 2) := by
  rw [bit_eq_digit, compress_eq, digit_pack 2 (by decide)]
  · exact ZMod.natCast_mod _ _
  · intro i; exact Nat.mod_lt _ (by decide)

theorem accum_eq (a : Nat) {m : Nat} (b : Fin m → Nat) :
    accum a (List.ofFn b) = ∑ k, digit 2 a k.val * b k := by
  induction m generalizing a with
  | zero => simp [accum]
  | succ m ih =>
    rw [List.ofFn_succ, accum, ih, Fin.sum_univ_succ]
    simp [digit, pow_succ', Nat.div_div_eq_div_mul]

theorem accum_expand (n m a : Nat) (b : Fin m → Nat) :
    accum a (List.ofFn (fun k => expand n (b k))) =
      pack 2048 (fun j : Fin n => ∑ k, digit 2 a k.val * digit 2 (b k) j.val) := by
  rw [accum_eq, pack_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [pack_mul, expand_eq]

theorem bit_product (n a : Nat) (hn : n < 2048) (b : Fin n → Nat) (j : Fin n) :
    bit (compress n (accum a (List.ofFn (fun k => expand n (b k))))) j.val =
      ∑ k, bit a k.val * bit (b k) j.val := by
  rw [bit_compress, accum_expand, digit_pack 2048 (by decide)]
  · simp only [Nat.cast_sum, Nat.cast_mul, bit_eq_digit]
  · intro j
    have hle : (∑ k : Fin n, digit 2 a k.val * digit 2 (b k) j.val) ≤ n := by
      calc
        _ ≤ ∑ _k : Fin n, 1 := by
          apply Finset.sum_le_sum
          intro k _
          have ha : digit 2 a k.val ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
          have hb : digit 2 (b k) j.val ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
          simpa using Nat.mul_le_mul ha hb
        _ = n := by simp
    omega

def decodeRows (n : Nat) (xs : List Nat) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => bit xs[i.val]! j.val

theorem ofFn_get! (xs : List Nat) :
    List.ofFn (fun i : Fin xs.length => xs[i.val]!) = xs := by
  conv_rhs => rw [← List.ofFn_get xs]
  congr 1
  funext i
  simp

theorem product_rows (n : Nat) (hn : n < 2048) (xs ys zs wide : List Nat)
    (hy : ys.length = n) (hw : wide = ys.map (expand n))
    (h : ∀ i : Fin n, compress n (accum xs[i.val]! wide) = zs[i.val]!) :
    decodeRows n xs * decodeRows n ys = decodeRows n zs := by
  subst n
  have hw' : wide = List.ofFn (fun i : Fin ys.length => expand ys.length ys[i.val]!) := by
    rw [hw]
    simpa only [List.map_ofFn, Function.comp_def] using
      congrArg (List.map (expand ys.length)) (ofFn_get! ys).symm
  ext i j
  change (∑ k : Fin ys.length, bit xs[i.val]! k.val * bit ys[k.val]! j.val) = _
  rw [← bit_product ys.length _ hn (fun k => ys[k.val]!) j, ← hw', h i]
  rfl

theorem product_sound (n : Nat) (hn : n < 2048) (xs ys zs wide : List Nat)
    (hx : xs.length = n) (hy : ys.length = n) (hw : wide = ys.map (expand n))
    (h : xs.map (fun a => compress n (accum a wide)) = zs) :
    decodeRows n xs * decodeRows n ys = decodeRows n zs := by
  apply product_rows n hn xs ys zs wide hy hw
  intro i
  have hi := congrArg (fun l : List Nat => l[i.val]?) h
  have hxi : i.val < xs.length := by simpa only [hx] using i.isLt
  have hzi : i.val < zs.length := by rw [← h, List.length_map]; exact hxi
  simpa [List.getElem?_map, hxi, hzi] using hi

theorem decodeRows_array (n : Nat) (a : Array Nat) :
    decodeRows n a.toList = decode n a := by
  ext i j
  simp [decodeRows, decode, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

theorem accum_append (a : Nat) (xs ys : List Nat) :
    accum a (xs ++ ys) = accum a xs + accum (a / 2 ^ xs.length) ys := by
  induction xs generalizing a with
  | nil => simp [accum]
  | cons x xs ih =>
    simp [accum, ih, Nat.add_assoc, pow_succ', Nat.div_div_eq_div_mul]

def accumChunks : Nat → List (List Nat) → Nat
  | _, [] => 0
  | a, b :: bs => accum a b + accumChunks (a / 2 ^ b.length) bs

theorem accumChunks_eq (a : Nat) (xs : List (List Nat)) :
    accumChunks a xs = accum a xs.flatten := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [accumChunks, List.flatten_cons, accum_append, ih]

theorem expand_add (m n a : Nat) :
    expand (m+n) a = expand m a + 2048 ^ m * expand n (a / 2 ^ m) := by
  induction m generalizing a with
  | zero => simp [expand]
  | succ m ih =>
    simp only [Nat.succ_add, expand, ih, pow_succ', Nat.div_div_eq_div_mul]
    simp [Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]

theorem compress_add (m n a : Nat) :
    compress (m+n) a = compress m a + 2 ^ m * compress n (a / 2048 ^ m) := by
  induction m generalizing a with
  | zero => simp [compress]
  | succ m ih =>
    simp only [Nat.succ_add, compress, ih, pow_succ', Nat.div_div_eq_div_mul]
    simp [Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]

def expandBlocks (width : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, a => expand width a + 2048 ^ width * expandBlocks width n (a / 2 ^ width)

def compressBlocks (width : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, a => compress width a + 2 ^ width * compressBlocks width n (a / 2048 ^ width)

theorem expandBlocks_eq (width blocks a : Nat) :
    expandBlocks width blocks a = expand (width * blocks) a := by
  induction blocks generalizing a with
  | zero => rfl
  | succ blocks ih =>
    calc
      expandBlocks width (blocks+1) a =
          expand width a + 2048 ^ width * expand (width * blocks) (a / 2 ^ width) := by
        rw [expandBlocks, ih]
      _ = expand (width + width * blocks) a := (expand_add width (width * blocks) a).symm
      _ = expand (width * (blocks+1)) a := by rw [Nat.mul_succ, Nat.add_comm]

theorem compressBlocks_eq (width blocks a : Nat) :
    compressBlocks width blocks a = compress (width * blocks) a := by
  induction blocks generalizing a with
  | zero => rfl
  | succ blocks ih =>
    calc
      compressBlocks width (blocks+1) a =
          compress width a + 2 ^ width * compress (width * blocks) (a / 2048 ^ width) := by
        rw [compressBlocks, ih]
      _ = compress (width + width * blocks) a := (compress_add width (width * blocks) a).symm
      _ = compress (width * (blocks+1)) a := by rw [Nat.mul_succ, Nat.add_comm]

/-- A matrix product assembled from checked row blocks. -/
theorem product_chunks (width blocks : Nat) (hn : width * blocks < 2048)
    (xs ys zs : List Nat) (wide : List (List Nat))
    (hx : xs.length = width * blocks) (hy : ys.length = width * blocks)
    (hw : wide.flatten = ys.map (expandBlocks width blocks))
    (h : xs.map (fun a => compressBlocks width blocks (accumChunks a wide)) = zs) :
    decodeRows (width * blocks) xs * decodeRows (width * blocks) ys =
      decodeRows (width * blocks) zs := by
  apply product_sound (width * blocks) hn xs ys zs wide.flatten hx hy
  · have he : expandBlocks width blocks = expand (width * blocks) :=
      funext (expandBlocks_eq width blocks)
    simpa only [he] using hw
  · simpa only [compressBlocks_eq, accumChunks_eq] using h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic

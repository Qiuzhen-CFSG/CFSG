module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.LongWords.Arithmetic
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.Checker

/-!
# Soundness of simultaneous packed matrix products

In base 2^w the mask selects digits equal to zero or one. Multiplying these
sparse digits by a row smaller than 2^w creates no carries between rows.
Extracting each digit therefore recovers the existing `listProduct` checker.
Its proved decoder bridge identifies the result with ordinary matrix
multiplication. This is a proof for arbitrary data, with no computed group
relations or density assumption. The application is the six long relators
of the unchanged ATLAS HSG1-P1.M.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.LongPacked

lemma chunk_zero (w x : Nat) : chunk w 0 x = x % 2^w := by simp [chunk]

lemma chunk_succ (w i x : Nat) : chunk w (i+1) x = chunk w i (x / 2^w) := by
  simp only [chunk, Nat.div_div_eq_div_mul, Nat.mul_add, Nat.mul_one, Nat.pow_add]
  rw [Nat.mul_comm (2^(w*i))]

lemma pack_div (w x : Nat) (xs : List Nat) (hx : x < 2^w) :
    pack w (x::xs) / 2^w = pack w xs := by
  simp only [pack, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt hx, Nat.zero_add]

lemma chunk_pack (w : Nat) (xs : List Nat) (hxs : ∀ x ∈ xs, x < 2^w) (i : Nat) :
    chunk w i (pack w xs) = xs[i]! := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [pack, chunk]
    | cons x xs => simp [chunk_zero, pack, Nat.mod_eq_of_lt (hxs x (by simp))]
  | succ i ih =>
    cases xs with
    | nil => simp [pack, chunk]
    | cons x xs =>
      rw [chunk_succ, pack_div w x xs (hxs x (by simp)), ih]
      · simp
      · intro x hx; exact hxs x (by simp [hx])

lemma chunk_and (w i x y : Nat) :
    chunk w i (x &&& y) = chunk w i x &&& chunk w i y := by
  simp [chunk, Nat.and_div_two_pow, Nat.and_mod_two_pow]

lemma chunk_xor (w i x y : Nat) :
    chunk w i (x ^^^ y) = chunk w i x ^^^ chunk w i y := by
  simp [chunk, Nat.xor_div_two_pow, Nat.xor_mod_two_pow]

lemma small_mul_div (a b p : Nat) (hp : 0 < p) (ha : a % p ≤ 1) (hb : b < p) :
    (a*b)/p = (a/p)*b := by
  have hlow : a % p * b < p := by
    calc a % p * b ≤ 1*b := Nat.mul_le_mul_right b ha
      _ = b := Nat.one_mul b
      _ < p := hb
  calc
    a*b/p = ((a%p + p*(a/p))*b)/p := by rw [Nat.mod_add_div]
    _ = (a/p)*b := by
      rw [Nat.add_mul, Nat.mul_assoc, Nat.add_mul_div_left _ _ hp,
        Nat.div_eq_of_lt hlow, Nat.zero_add]

lemma sparse_mul_div (w c b i : Nat) (hc : ∀ j, chunk w j c ≤ 1) (hb : b < 2^w) :
    c*b / 2^(w*i) = (c / 2^(w*i))*b := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Nat.mul_succ, Nat.pow_add, ← Nat.div_div_eq_div_mul, ih]
    simpa only [Nat.div_div_eq_div_mul] using small_mul_div _ _ _ (Nat.two_pow_pos w) (hc i) hb

lemma sparse_mul_chunk (w c b i : Nat) (hc : ∀ j, chunk w j c ≤ 1) (hb : b < 2^w) :
    chunk w i (c*b) = chunk w i c * b := by
  rw [chunk, sparse_mul_div w c b i hc hb, Nat.mul_mod]
  have hlow : chunk w i c * b < 2^w := by
    calc chunk w i c * b ≤ 1*b := Nat.mul_le_mul_right b (hc i)
      _ = b := Nat.one_mul b
      _ < 2^w := hb
  rw [Nat.mod_eq_of_lt hb]
  exact Nat.mod_eq_of_lt hlow

lemma chunk_mask (w n i : Nat) (hw : 0 < w) :
    chunk w i (pack w (List.replicate n 1)) = if i < n then 1 else 0 := by
  rw [chunk_pack]
  · by_cases hi : i < n <;> simp [hi]
  · intro x hx
    have : x = 1 := (List.mem_replicate.mp hx).2
    subst x
    exact Nat.one_lt_two_pow (by omega)

lemma masked_sparse (w x mask k : Nat) (hm : ∀ i, chunk w i mask ≤ 1) :
    ∀ i, chunk w i ((x >>> k) &&& mask) ≤ 1 := by
  intro i
  rw [chunk_and]
  exact Nat.le_trans Nat.and_le_right (hm i)

lemma chunk_shift_bit (w i x k : Nat) (hk : k < w) :
    (chunk w i (x >>> k)) % 2 = if (chunk w i x).testBit k then 1 else 0 := by
  have hbit : (chunk w i (x >>> k)).testBit 0 = (chunk w i x).testBit k := by
    simp only [chunk, Nat.testBit_mod_two_pow]
    simp only [Nat.testBit_div_two_pow, Nat.testBit_shiftRight]
    simp only [show 0 < w by omega, hk, decide_true, Bool.true_and, Nat.zero_add,
      Nat.add_comm k]
  have hmod (z : Nat) : z % 2 = if z.testBit 0 then 1 else 0 := by
    simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one, decide_eq_true_eq]
    split <;> omega
  rw [hmod]
  simp only [hbit]

lemma product_chunk (w x mask start i : Nat) (bs : List Nat)
    (hm : ∀ j, chunk w j mask ≤ 1) (hi : chunk w i mask = 1)
    (hs : start + bs.length ≤ w) (hb : ∀ b ∈ bs, b < 2^w) :
    chunk w i (product w x mask start bs) =
      PackedBinaryRows.listProduct (chunk w i x) start bs := by
  induction bs generalizing start with
  | nil => simp [product, chunk, PackedBinaryRows.listProduct]
  | cons b bs ih =>
    rw [product, chunk_xor, sparse_mul_chunk _ _ _ _ (masked_sparse _ _ _ _ hm)
      (hb b (by simp)), chunk_and, hi, Nat.and_one_is_mod,
      chunk_shift_bit w i x start (by simp only [List.length_cons] at hs; omega)]
    rw [ih (start+1) (by simp only [List.length_cons] at hs; omega) (fun b h => hb b (by simp [h]))]
    simp only [PackedBinaryRows.listProduct]
    split <;> simp
lemma row_certificate (w : Nat) (hw : 0 < w) (a b c : Array Nat)
    (ha : ∀ x ∈ a.toList, x < 2^w)
    (hb : ∀ x ∈ b.toList, x < 2^w)
    (hc : ∀ x ∈ c.toList, x < 2^w)
    (hsize : b.size = w)
    (h : product w (pack w a.toList) (pack w (List.replicate w 1)) 0 b.toList =
      pack w c.toList) (i : Fin w) :
    PackedBinaryRows.listProduct a[i.val]! 0 b.toList = c[i.val]! := by
  have hm (j : Nat) : chunk w j (pack w (List.replicate w 1)) ≤ 1 := by
    rw [chunk_mask w w j hw]
    split <;> omega
  have hi : chunk w i.val (pack w (List.replicate w 1)) = 1 := by
    rw [chunk_mask w w i.val hw, if_pos i.isLt]
  have he := congrArg (chunk w i.val) h
  rw [product_chunk _ _ _ _ _ _ hm hi (by simpa using Nat.le_of_eq hsize) hb,
    chunk_pack w a.toList ha, chunk_pack w c.toList hc] at he
  simpa only [Array.getElem!_toList] using he

private lemma all_lt_iff (xs : List Nat) (bound : Nat) :
    xs.all (fun x => decide (x < bound)) = true ↔ ∀ x ∈ xs, x < bound := by
  simp only [List.all_eq_true, decide_eq_true_eq]

-- Only the literal row bound 2^1408 is reduced here; this is not a heartbeat limit.
set_option exponentiation.threshold 1408 in
lemma boundedRows_iff (a : Array Nat) :
    BoundedRows a ↔ ∀ x ∈ a.toList, x < 2^1408 :=
  all_lt_iff a.toList (2^1408)

/-- Each numerical certificate gives the literal ordinary matrix product. -/
theorem productCertificate_sound (a b c : Array Nat)
    (ha : BoundedRows a) (hb : BoundedRows b) (hc : BoundedRows c)
    (hsize : b.size = 1408) (h : ProductCertificate a b c) :
    Thompson.BinaryMatrix.decode 1408 a * Thompson.BinaryMatrix.decode 1408 b =
      Thompson.BinaryMatrix.decode 1408 c := by
  apply Thompson.BinaryMatrix.decode_mul
  intro i
  rw [PackedBinaryRows.rowProduct_eq_listProduct _ _ _ hsize]
  exact row_certificate 1408 (by decide) a b c
    ((boundedRows_iff a).mp ha) ((boundedRows_iff b).mp hb)
    ((boundedRows_iff c).mp hc) hsize h i

theorem identity_bounded : BoundedRows identityRows := by
  unfold BoundedRows
  decide +kernel

theorem identity_decode : Thompson.BinaryMatrix.decode 1408 identityRows = 1 := by
  ext i j
  simp [Thompson.BinaryMatrix.decode, identityRows, Thompson.BinaryMatrix.bit,
    Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.LongPacked

module
public import Theory.SpecificGroups.Thompson.Model.Order.Cosets.Bounds
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix

/-!
# Certified binary row-word evaluation

Packed rows are transported along positive words in the exact Thompson matrix
carrier. Intermediate rows form a certificate: checking every transition proves
the final row identity by induction. The words below transcribe `localA` and
`localB`, replacing generator inverses using the certified square and cube
relations. The overwrite in the second ATLAS word is retained.

Source words and attribution: `Model/Order/source/README.md` and
`ThG1-max1W1`. The binary arithmetic is proved in `BinaryMatrix`.
-/

namespace Thompson.OrderCertificate.Separation
open scoped BigOperators

@[expose] public def row (r : ℕ) : Fin 248 → ZMod 2 :=
  fun j => BinaryMatrix.bit r j.val

public theorem row_product (r : ℕ) (a : Array ℕ) :
    row (BinaryMatrix.rowProduct r a 248) =
      Matrix.vecMul (row r) (BinaryMatrix.decode 248 a) := by
  funext j
  rw [row, BinaryMatrix.bit_rowProduct]
  exact (Fin.sum_univ_eq_sum_range (fun k =>
    BinaryMatrix.bit r k * BinaryMatrix.bit a[k]! j.val) 248).symm

@[expose] public def wordValue (w : List Bool) : Model :=
  (w.map cosetGenerators).prod

public theorem wordValue_nil : wordValue [] = 1 := rfl
public theorem wordValue_cons (b : Bool) (w : List Bool) :
    wordValue (b :: w) = cosetGenerators b * wordValue w := rfl
public theorem wordValue_append (w v : List Bool) :
    wordValue (w ++ v) = wordValue w * wordValue v := by
  simp [wordValue]

@[expose] public def step (r : ℕ) (b : Bool) : ℕ :=
  BinaryMatrix.rowProduct r (if b then atlasBRows else atlasARows) 248

public theorem row_step (r : ℕ) (b : Bool) :
    row (step r b) = Matrix.vecMul (row r) (matrixHom (cosetGenerators b)) := by
  cases b <;> exact row_product r _

@[expose] public def runWord (r : ℕ) (w : List Bool) : ℕ := w.foldl step r

public theorem row_runWord (r : ℕ) (w : List Bool) :
    row (runWord r w) = Matrix.vecMul (row r) (matrixHom (wordValue w)) := by
  induction w generalizing r with
  | nil => simp [runWord, wordValue]
  | cons b w ih =>
    change row (runWord (step r b) w) = _
    rw [ih, row_step, Matrix.vecMul_vecMul, wordValue_cons, map_mul]



@[expose] public def repeatWord (n : ℕ) (w : List Bool) : List Bool :=
  (List.replicate n w).flatten

public theorem wordValue_repeatWord (n : ℕ) (w : List Bool) :
    wordValue (repeatWord n w) = wordValue w ^ n := by
  induction n with
  | zero => simp [repeatWord, wordValue]
  | succ n ih =>
    simp only [repeatWord, List.replicate_succ, List.flatten_cons]
    rw [wordValue_append, ← repeatWord, ih, pow_succ']

@[expose] public def localAWord : List Bool :=
  repeatWord 8 [true, true, false] ++ [false] ++ repeatWord 8 [false, true]

@[expose] public def localBWord : List Bool :=
  let r3 := [false, true]
  let r4 := r3 ++ [true]
  let r5 := r3 ++ r4
  let r6 := r3 ++ r5
  let r7 := r6 ++ r3
  let r8 := r7 ++ r4
  let r9 := r3 ++ r8
  repeatWord 5 (r7 ++ r9)

public theorem wordValue_localAWord : wordValue localAWord = localA := by
  have ha : generatorA⁻¹ = generatorA := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using generatorA_sq
  have hb : generatorB⁻¹ = generatorB * generatorB := by
    apply inv_eq_of_mul_eq_one_right
    calc
      generatorB * (generatorB * generatorB) = generatorB ^ 3 := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ', pow_two]
      _ = 1 := generatorB_cube
  simp only [localAWord, wordValue_append, wordValue_repeatWord, wordValue_cons,
    wordValue_nil, cosetGenerators, mul_one, localA, ← inv_pow, mul_inv_rev, ha, hb, mul_assoc]

public theorem wordValue_localBWord : wordValue localBWord = localB := by
  simp only [localBWord, wordValue_repeatWord, wordValue_append, wordValue_cons,
    wordValue_nil, mul_one]
  rfl

public theorem runWord_of_trace (w : List Bool) (t : Array ℕ)
    (h : ∀ k : Fin w.length, step t[k.val]! w[k.val] = t[k.val + 1]!) :
    runWord t[0]! w = t[w.length]! := by
  have hp : ∀ k, k ≤ w.length → runWord t[0]! (w.take k) = t[k]! := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have hlt : k < w.length := hk
      rw [List.take_succ_eq_append_getElem hlt]
      simp only [runWord, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change step (runWord t[0]! (w.take k)) w[k] = _
      rw [ih (Nat.le_of_lt hlt)]
      exact h ⟨k, hlt⟩
  simpa only [List.take_length] using hp w.length le_rfl

end Thompson.OrderCertificate.Separation

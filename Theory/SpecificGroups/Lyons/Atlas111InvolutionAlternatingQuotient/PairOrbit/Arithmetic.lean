module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Arithmetic

/-!
# Sequential packed products and symmetric residue checks

The orbit certificates compare two matrix products over F₅. `fastProduct`
reads the packed scalar row by successive division, avoiding repeated powers.
`digitsCongr` reduces both product rows modulo five. Its soundness, together
with the carry-free bound already proved for radix 3125, yields an actual
matrix equality. No external computation is trusted.

Source: the finite orbit for GLS3 section 5.3, Lyons table, printed p.278;
attributed matrix data in `../../Atlas111Source/`.
-/

namespace Lyons.SimplicityCertificate.AlternatingQuotient.PairOrbit

open Atlas111WordCertificate

@[expose] public def fastProduct (a : ℕ) (rows : Fin 111 → ℕ) (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => a % radix * rows (Fin.ofNat 111 start) +
      fastProduct (a / radix) rows (start + 1) n

public theorem fastProduct_eq (a : ℕ) (rows : Fin 111 → ℕ) (start n : ℕ) :
    fastProduct a rows start n =
      ∑ j : Fin n, digit a j.val * rows (Fin.ofNat 111 (start + j.val)) := by
  induction n generalizing a start with
  | zero => simp [fastProduct]
  | succ n ih =>
    rw [fastProduct, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.add_zero, digit, pow_zero, Nat.div_one,
      Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.add_assoc, Nat.add_comm 1 j.val]

public theorem fastProduct_zero (a : ℕ) (rows : Fin 111 → ℕ) :
    fastProduct a rows 0 111 = rowProduct a rows 111 := by
  rw [fastProduct_eq, rowProduct_eq]
  simp only [Nat.zero_add]

@[expose] public def digitsCongr : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | n + 1, a, b => (a % radix % 5 == b % radix % 5) &&
      digitsCongr n (a / radix) (b / radix)

public theorem digitsCongr_sound (n a b : ℕ) (h : digitsCongr n a b = true) :
    ∀ j < n, digit a j % 5 = digit b j % 5 := by
  induction n generalizing a b with
  | zero => intro j hj; omega
  | succ n ih =>
    simp only [digitsCongr, Bool.and_eq_true, beq_iff_eq] at h
    intro j hj
    cases j with
    | zero => simpa [digit] using h.1
    | succ j => simpa only [digit_succ] using ih _ _ h.2 j (by omega)

public theorem decode_intertwine (a b c d : Fin 111 → ℕ)
    (ha : ∀ i, small 111 (a i) = true) (hb : ∀ i, small 111 (b i) = true)
    (hc : ∀ i, small 111 (c i) = true) (hd : ∀ i, small 111 (d i) = true)
    (h : ∀ i, digitsCongr 111 (fastProduct (a i) b 0 111)
      (fastProduct (c i) d 0 111) = true) :
    decode a * decode b = decode c * decode d := by
  ext i j
  change (∑ k : Fin 111, (digit (a i) k.val : ZMod 5) *
      (digit (b k) j.val : ZMod 5)) =
    (∑ k : Fin 111, (digit (c i) k.val : ZMod 5) *
      (digit (d k) j.val : ZMod 5))
  simp only [← Nat.cast_mul, ← Nat.cast_sum]
  rw [← rowProduct_digit _ _ (ha i) hb j, ← rowProduct_digit _ _ (hc i) hd j]
  have he := digitsCongr_sound _ _ _ (h i) j.val j.isLt
  rw [fastProduct_zero, fastProduct_zero] at he
  simpa only [ZMod.natCast_mod] using congrArg (fun n : ℕ => (n : ZMod 5)) he

end Lyons.SimplicityCertificate.AlternatingQuotient.PairOrbit

module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.Blocks
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density518.Setup

/-!
# Soundness of the rank-one certificates

The packed row checks below are interpreted as equations on the literal ATLAS
HSG1-f2r518B0 matrices. Two intermediate products B² and A B², together with
B³, certify membership of D directly; no generator relations are assumed.
The complementary inverse and null vectors then feed the finite-algebra
projection lemma. See `RankOne/source/README.md` for certificate provenance.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density518.RankOne
open Matrix RowArithmetic Thompson.BinaryMatrix

def squareTarget (i : ℕ) (s c : Array ℕ) : ℕ :=
  dRows[i]! ^^^ s[i]! ^^^ c[i]! ^^^ 2 ^ i

def complementMask (i : ℕ) : ℕ :=
  dRows[i]! ^^^ (if imageColumn.testBit i then functionalRow else 0)

theorem batch_transfer (rows : List ℕ) (masks outs : Array ℕ)
    (f g : ℕ → ℕ) (start count : ℕ)
    (hm : ∀ i : Fin count, masks[i.val]! = f (start + i.val))
    (ho : ∀ i : Fin count, outs[i.val]! = g (start + i.val))
    (hc : ∀ i : Fin count, combine rows masks[i.val]! = outs[i.val]!)
    (i : ℕ) (hlo : start ≤ i) (hhi : i < start + count) :
    combine rows (f i) = g i := by
  let j : Fin count := ⟨i - start, by omega⟩
  have hj : start + j.val = i := by dsimp [j]; omega
  simpa only [hm j, ho j, hj] using hc j

theorem product_of_checked (lhs rhs out : Array ℕ) (hs : rhs.size = 518)
    (h : ∀ i : Fin 518, combine rhs.toList lhs[i.val]! = out[i.val]!) :
    decode 518 lhs * decode 518 rhs = decode 518 out := by
  rw [← matrix_toList, ← matrix_toList, ← matrix_toList]
  apply matrix_product
  · simpa using hs
  · simpa only [Array.getElem!_toList] using h

theorem vector_xor (x y : ℕ) : vector 518 (x ^^^ y) = vector 518 x + vector 518 y := by
  funext j
  exact bit_xor x y j.val

theorem vector_zero : vector 518 0 = 0 := by
  funext j
  simp [vector, bit]

theorem vector_single (i : Fin 518) : vector 518 (2 ^ i.val) = (1 : Matrix518) i := by
  funext j
  simp [vector, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

theorem square_sum_of_checked (s c x : Array ℕ) (hs : x.size = 518)
    (h : ∀ i : Fin 518, combine x.toList x[i.val]! = squareTarget i.val s c) :
    decode 518 x * decode 518 x = D + decode 518 s + decode 518 c + 1 := by
  funext i
  rw [decode_product_row _ _ _ i _ hs (h i)]
  change vector 518 (dRows[i.val]! ^^^ s[i.val]! ^^^ c[i.val]! ^^^ 2 ^ i.val) = _
  rw [vector_xor, vector_xor, vector_xor, vector_single]
  rfl

theorem complement_row (i : Fin 518) :
    (D + vecMulVec u v) i = vector 518 (complementMask i.val) := by
  rw [complementMask, vector_xor]
  funext j
  change bit dRows[i.val]! j.val + bit imageColumn i.val * bit functionalRow j.val = _
  cases hi : imageColumn.testBit i.val <;> simp [vector, bit, hi]

theorem complement_of_checked
    (h : ∀ i : Fin 518, combine complementInverseRows.toList (complementMask i.val) = 2 ^ i.val) :
    (D + vecMulVec u v) * E = 1 := by
  funext i
  change vecMul ((D + vecMulVec u v) i) E = _
  rw [complement_row]
  have hv := vector_combine complementInverseRows.toList 518 518
    (by simpa using Blocks.e_size) (complementMask i.val)
  rw [matrix_toList, h i, vector_single] at hv
  exact hv.symm

end Representation.HigmanSims.LargeModels.Binary.Large.Density518.RankOne

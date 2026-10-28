module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Theory.LinearAlgebra.PackedBinaryRows
public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCriterion

/-!
# Binary row certificates and the rank-one density criterion

Sequential packed row products decode to matrix multiplication over GF(2).
Checked orbit recurrences and inverse basis matrices provide the spanning
hypotheses of the existing rank-one matrix criterion. This checker is used by
the literal HS degree-56 and degree-132 density certificates.

Source data and attribution: `../source/README.md`. The orbit argument follows
the repository's G2 cycle-factor and M22 dual induced-factor proofs.
-/

@[expose] public section
open Matrix Thompson.BinaryMatrix
namespace Representation.HigmanSims.LargeModels.Binary.Small.Packed

def vector {n : ℕ} (x : ℕ) : Fin n → ZMod 2 := fun i => bit x i.val

theorem rowProduct_list (x : ℕ) (a : Array ℕ) (n : ℕ) (ha : a.size = n) :
    rowProduct x a n = PackedBinaryRows.listProduct x 0 a.toList := by
  have hr (k : ℕ) : rowProduct x a k =
      PackedBinaryRows.rowRange x (fun j => a[j]!) 0 k := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [rowProduct, PackedBinaryRows.rowRange, Nat.zero_add, ih]
  rw [hr]
  exact PackedBinaryRows.rowRange_eq_blockProduct x (fun j => a[j]!) 0 n a ha (fun _ => by rw [Nat.zero_add])

theorem mul_checked {n : ℕ} (a b c : Array ℕ) (hb : b.size = n)
    (h : ∀ i : Fin n, PackedBinaryRows.listProduct a[i.val]! 0 b.toList = c[i.val]!) :
    decode n a * decode n b = decode n c := by
  apply decode_mul
  intro i
  rw [rowProduct_list _ _ _ hb, h]

theorem inverse_checked {n : ℕ} (a b : Array ℕ) (hb : b.size = n)
    (h : ∀ i : Fin n, PackedBinaryRows.listProduct a[i.val]! 0 b.toList = 2 ^ i.val) :
    decode n a * decode n b = 1 := by
  apply decode_mul_one
  intro i
  rw [rowProduct_list _ _ _ hb, h]

theorem add_checked {n : ℕ} (a b c : Array ℕ)
    (h : ∀ i : Fin n, a[i.val]! ^^^ b[i.val]! = c[i.val]!) :
    decode n a + decode n b = decode n c := by
  ext i j
  exact (bit_xor _ _ _).symm.trans (congrArg (fun x => bit x j.val) (h i))

theorem one_checked {n : ℕ} (a : Array ℕ)
    (h : ∀ i : Fin n, a[i.val]! = 2 ^ i.val) : decode n a = 1 := by
  ext i j
  simp [decode, h i, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

theorem outer_checked {n : ℕ} (a : Array ℕ) (u v : ℕ)
    (h : ∀ i : Fin n, a[i.val]! = if u.testBit i.val then v else 0) :
    decode n a = vecMulVec (vector u) (vector v) := by
  ext i j
  simp only [decode, h i, vecMulVec_apply, vector, bit]
  cases u.testBit i.val <;> simp

theorem transpose_checked {n : ℕ} (a b : Array ℕ)
    (h : ∀ i j : Fin n, a[i.val]!.testBit j.val = b[j.val]!.testBit i.val) :
    decode n a = (decode n b)ᵀ := by
  ext i j
  simp only [decode, transpose_apply, bit, h i j]

theorem vecMul_checked {n : ℕ} (a : Array ℕ) (x y : ℕ) (ha : a.size = n)
    (h : PackedBinaryRows.listProduct x 0 a.toList = y) :
    vecMul (vector x) (decode n a) = vector y := by
  funext j
  change (∑ k : Fin n, bit x k.val * bit a[k.val]! j.val) = bit y j.val
  rw [Fin.sum_univ_eq_sum_range (fun k => bit x k * bit a[k]! j.val),
    ← bit_rowProduct, rowProduct_list _ _ _ ha, h]

theorem span_rows_of_inverse {n : ℕ} (a b : Array ℕ)
    (h : decode n b * decode n a = 1) :
    Submodule.span (ZMod 2) (Set.range (fun i : Fin n => vector (n := n) a[i.val]!)) = ⊤ := by
  change Submodule.span (ZMod 2) (Set.range (decode n a).row) = ⊤
  rw [← range_vecMulLinear, LinearMap.range_eq_top]
  intro v
  refine ⟨vecMul v (decode n b), ?_⟩
  change vecMul (vecMul v (decode n b)) (decode n a) = v
  rw [vecMul_vecMul, h, vecMul_one]

theorem column_realizations {n : ℕ}
    (Q : Subalgebra (ZMod 2) (Matrix (Fin (n+1)) (Fin (n+1)) (ZMod 2)))
    (A : Fin 2 → Matrix (Fin (n+1)) (Fin (n+1)) (ZMod 2))
    (hA : ∀ a, A a ∈ Q) (xs : Fin (n+1) → ℕ)
    (p : Fin n → Fin (n+1)) (a : Fin n → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, (A (a i)).mulVec (vector (xs (p i))) = vector (xs i.succ)) :
    ∀ i, ∃ L : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod 2),
      L ∈ Q ∧ L.mulVec (vector (xs 0)) = vector (xs i) := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, one_mulVec _⟩
    | succ i =>
      obtain ⟨L, hL, he⟩ := ih (p i) (hp i)
      refine ⟨A (a i) * L, Q.mul_mem (hA _) hL, ?_⟩
      rw [← mulVec_mulVec, he, hs i]

theorem row_realizations {n : ℕ}
    (Q : Subalgebra (ZMod 2) (Matrix (Fin (n+1)) (Fin (n+1)) (ZMod 2)))
    (A : Fin 2 → Matrix (Fin (n+1)) (Fin (n+1)) (ZMod 2))
    (hA : ∀ a, A a ∈ Q) (xs : Fin (n+1) → ℕ)
    (p : Fin n → Fin (n+1)) (a : Fin n → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, vecMul (vector (xs (p i))) (A (a i)) = vector (xs i.succ)) :
    ∀ i, ∃ R : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod 2),
      R ∈ Q ∧ vecMul (vector (xs 0)) R = vector (xs i) := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    cases i using Fin.cases with
    | zero => exact ⟨1, Q.one_mem, vecMul_one _⟩
    | succ i =>
      obtain ⟨R, hR, he⟩ := ih (p i) (hp i)
      refine ⟨R * A (a i), Q.mul_mem hR (hA _), ?_⟩
      rw [← vecMul_vecMul, he, hs i]

theorem full_of_orbits {n : ℕ}
    (Q : Subalgebra (ZMod 2) (Matrix (Fin (n+1)) (Fin (n+1)) (ZMod 2)))
    (A : Fin 2 → Matrix (Fin (n+1)) (Fin (n+1)) (ZMod 2))
    (hA : ∀ a, A a ∈ Q) (cols rows ci ri : Array ℕ)
    (cp rp : Fin n → Fin (n+1)) (ca ra : Fin n → Fin 2)
    (hcp : ∀ i, cp i < i.succ) (hrp : ∀ i, rp i < i.succ)
    (hcs : ∀ i, (A (ca i)).mulVec (vector cols[(cp i).val]!) = vector cols[i.val+1]!)
    (hrs : ∀ i, vecMul (vector rows[(rp i).val]!) (A (ra i)) = vector rows[i.val+1]!)
    (hci : decode (n+1) ci * decode (n+1) cols = 1)
    (hri : decode (n+1) ri * decode (n+1) rows = 1)
    (huv : vecMulVec (vector cols[0]!) (vector rows[0]!) ∈ Q) : Q = ⊤ := by
  classical
  choose L hL heL using column_realizations Q A hA (fun i => cols[i.val]!) cp ca hcp hcs
  choose R hR heR using row_realizations Q A hA (fun i => rows[i.val]!) rp ra hrp hrs
  apply G2DerivedPermutationFiltration.CycleMatrixCriterion.algebra_eq_top_of_rank_one Q
    (vector cols[0]!) (vector rows[0]!) L R hL hR huv
  · rw [show (fun i => (L i).mulVec (vector cols[0]!)) =
      (fun i : Fin (n+1) => vector (n := n+1) cols[i.val]!) from funext heL]
    exact span_rows_of_inverse cols ci hci
  · rw [show (fun i => vecMul (vector rows[0]!) (R i)) =
      (fun i : Fin (n+1) => vector (n := n+1) rows[i.val]!) from funext heR]
    exact span_rows_of_inverse rows ri hri

end Representation.HigmanSims.LargeModels.Binary.Small.Packed

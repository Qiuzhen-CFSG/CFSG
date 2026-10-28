module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.Data
public import Mathlib.Data.List.OfFn

/-!
# Packed binary column arithmetic for the M₁₁ filtration

Decoding a recursively XOR-combined list is matrix multiplication over F₂.
The finite certificates consequently check natural-number equalities, while
these structural lemmas justify their interpretation as matrix identities.
Source application: Aschbacher–Smith G.7.3(2); witness conventions in
`../source/README.md`.
-/

@[expose] public section
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.CertificateFiltration.Packed

def bit (v r : ℕ) : ZMod 2 := if v.testBit r then 1 else 0

def combineList : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, v => (if v.testBit 0 then c else 0) ^^^ combineList cs (v / 2)

theorem bit_xor (a b r : ℕ) : bit (a ^^^ b) r = bit a r + bit b r := by
  simp only [bit, Nat.testBit_xor]
  cases a.testBit r <;> cases b.testBit r <;> decide

theorem bit_combine (n : ℕ) (c : Fin n → ℕ) (v r : ℕ) :
    bit (combineList (List.ofFn c) v) r = ∑ j, bit (c j) r * bit v j.val := by
  induction n generalizing v with
  | zero => simp [List.ofFn_zero, combineList, bit]
  | succ n ih =>
    rw [List.ofFn_succ, combineList, bit_xor, ih, Fin.sum_univ_succ]
    congr 1
    · cases h : v.testBit 0 <;> simp [bit, h]
    · apply Finset.sum_congr rfl
      intro j _
      simp only [bit, Nat.testBit_div_two, Fin.val_succ]

theorem ofFn_getD (n : ℕ) (cs : List ℕ) (h : cs.length = n) :
    List.ofFn (fun j : Fin n => cs[j.val]!) = cs := by
  subst n
  simp

def matrix {n : ℕ} (cs : List ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun r j => bit cs[j.val]! r.val

theorem matrix_mul_column {n : ℕ} (cs ds : List ℕ) (h : cs.length = n)
    (r j : Fin n) :
    (matrix cs * matrix ds : Matrix (Fin n) (Fin n) (ZMod 2)) r j = bit (combineList cs ds[j.val]!) r.val := by
  rw [← ofFn_getD n cs h, bit_combine]
  simp [matrix, Matrix.mul_apply]

theorem matrix_mul_eq {n : ℕ} (as bs cs ds : List ℕ)
    (ha : as.length = n) (hc : cs.length = n)
    (h : ∀ j : Fin n, combineList as bs[j.val]! = combineList cs ds[j.val]!) :
    (matrix as : Matrix (Fin n) (Fin n) (ZMod 2)) * matrix bs = matrix cs * matrix ds := by
  ext r j
  rw [matrix_mul_column as bs ha, matrix_mul_column cs ds hc, h]

theorem matrix_mul_one {n : ℕ} (as bs : List ℕ) (ha : as.length = n)
    (h : ∀ j : Fin n, combineList as bs[j.val]! = 2 ^ j.val) :
    (matrix as : Matrix (Fin n) (Fin n) (ZMod 2)) * matrix bs = 1 := by
  ext r j
  rw [matrix_mul_column as bs ha, h]
  simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff, eq_comm]

end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.CertificateFiltration.Packed

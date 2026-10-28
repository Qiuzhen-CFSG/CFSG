module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Data

/-!
# Linear certificate arithmetic for the max4 commutant

Packed masks are linear forms over GF(2); XOR and row scans preserve their
semantics. These elementary lemmas are adapted from the project's
`AffineRestriction.Binary` without its unrelated centralizer imports.
The application is the exhaustive commutant calculation described in
`CharacteristicTwo/source/README.md`.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof
open GeneratorCertificates
open scoped Matrix

/-- Evaluation of a binary mask as a linear form. -/
def ev {n : ℕ} (x : Fin n → ZMod 2) (r : ℕ) : ZMod 2 :=
  ∑ i, bit r i.val * x i

lemma ev_zero {n : ℕ} (x : Fin n → ZMod 2) : ev x 0 = 0 := by simp [ev, bit]
lemma ev_xor {n : ℕ} (x : Fin n → ZMod 2) (r s : ℕ) :
    ev x (r ^^^ s) = ev x r + ev x s := by
  simp only [ev, bit_xor, add_mul, Finset.sum_add_distrib]
lemma ev_unit {n : ℕ} (x : Fin n → ZMod 2) (i : Fin n) : ev x (2 ^ i.val) = x i := by
  simp [ev, bit, Nat.testBit_two_pow, Fin.val_inj]
lemma ev_xorList {n : ℕ} (x : Fin n → ZMod 2) (rs : List ℕ) :
    ev x (xorList rs) = (rs.map (ev x)).sum := by
  induction rs with
  | nil => exact ev_zero x
  | cons a as ih => simp only [xorList, ev_xor, ih, List.map_cons, List.sum_cons]

/-- Sequential multiplication of a binary row by a table of packed columns. -/
def scan : ℕ → List ℕ → ℕ
  | _, [] => 0
  | x, y :: ys => (if x.testBit 0 then y else 0) ^^^ scan (x >>> 1) ys

lemma scan_ofFn {n : ℕ} (x : ℕ) (f : Fin n → ℕ) :
    scan x (List.ofFn f) =
      xorList (List.ofFn (fun i => if x.testBit i.val then f i else 0)) := by
  induction n generalizing x with
  | zero => simp [scan, xorList]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, scan, xorList, ih]
    congr 1
    apply congrArg xorList
    apply congrArg List.ofFn
    funext i
    simp [Nat.testBit_shiftRight, Nat.add_comm]

lemma ofFn_get {α : Type*} {n : ℕ} (v : Vector α n) : List.ofFn v.get = v.toList := by
  exact Vector.toList_ofFn.symm.trans (congrArg Vector.toList (Vector.ofFn_getElem (xs := v)))

lemma bit_scan {n : ℕ} (x : ℕ) (ys : Vector ℕ n) (j : ℕ) :
    bit (scan x ys.toList) j = ev (fun i => bit (ys.get i) j) x := by
  rw [← ofFn_get, scan_ofFn, bit_xorList, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  cases h : x.testBit i.val <;> simp [bit, h]


lemma ev_scan {n d : ℕ} (x : Fin n → ZMod 2) (c : ℕ) (rs : Vector ℕ d) :
    ev x (scan c rs.toList) = ∑ i : Fin d, bit c i.val * ev x (rs.get i) := by
  rw [← ofFn_get, scan_ofFn, ev_xorList, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  cases h : c.testBit i.val <;> simp [h, bit, ev_zero]


def row (r : ℕ) : Fin 112 → ZMod 2 := fun j => bit r j.val

def evaluate (c : Fin 448 → ZMod 2) (rs : Vector ℕ 112) : Fin 112 → ZMod 2 :=
  fun j => ev c (rs.get j)

lemma row_scan (r : ℕ) (A : Vector ℕ 112) :
    row (scan r A.toList) = row r ᵥ* decodeRows A := by
  funext j
  exact bit_scan r A j.val

lemma row_unit (i : Fin 112) : row (2 ^ i.val) = Pi.single i 1 := by
  funext j
  simp [row, bit, Nat.testBit_two_pow, Pi.single_apply, Fin.ext_iff, eq_comm]

lemma evaluate_mul (c : Fin 448 → ZMod 2) (rs ts cols : Vector ℕ 112)
    (A : BinaryMatrix) (hc : ∀ i j, bit (cols.get j) i.val = A i j)
    (ht : ∀ j, scan (cols.get j) rs.toList = ts.get j) :
    evaluate c rs ᵥ* A = evaluate c ts := by
  funext j
  rw [evaluate, ← ht, ev_scan]
  simp only [Matrix.vecMul, dotProduct, evaluate, hc, mul_comm]

lemma commute_row (M A : BinaryMatrix) (h : Commute M A) (r : Fin 112 → ZMod 2) :
    (r ᵥ* A) ᵥ* M = (r ᵥ* M) ᵥ* A := by
  rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, h.eq]

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof

module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.Coordinates

/-!
# Binary elimination certificates for the mixed restriction

Masks denote linear forms over F₂. A triangular table proves injectivity on
its free coordinates; a checked family in its kernel then spans that kernel.
The elimination trace is an explicit XOR of source equations and preceding
rows, checked in the kernel. This is the finite matrix calculation described
in LinearMembership/source/README.md, in the original ATLAS coordinates.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.FiniteAlgebra
open GeneratorCertificates

/-- Evaluation of a binary mask as a linear form. -/
def ev {n : ℕ} (x : Fin n → ZMod 2) (r : ℕ) : ZMod 2 :=
  ∑ i, bit r i.val * x i

lemma ev_zero {n : ℕ} (x : Fin n → ZMod 2) : ev x 0 = 0 := by simp [ev, bit]
lemma ev_xor {n : ℕ} (x : Fin n → ZMod 2) (r s : ℕ) :
    ev x (r ^^^ s) = ev x r + ev x s := by
  simp only [ev, bit_xor, add_mul, Finset.sum_add_distrib]
lemma ev_add {n : ℕ} (x y : Fin n → ZMod 2) (r : ℕ) :
    ev (x + y) r = ev x r + ev y r := by
  simp [ev, mul_add, Finset.sum_add_distrib]
lemma ev_smul {n : ℕ} (c : ZMod 2) (x : Fin n → ZMod 2) (r : ℕ) :
    ev (c • x) r = c * ev x r := by
  simp [ev, Finset.mul_sum, mul_left_comm]
lemma ev_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin n → ZMod 2) (r : ℕ) :
    ev (∑ i ∈ s, f i) r = ∑ i ∈ s, ev (f i) r := by
  simp only [ev, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm
lemma ev_unit {n : ℕ} (x : Fin n → ZMod 2) (i : Fin n) : ev x (2 ^ i.val) = x i := by
  simp [ev, bit, Nat.testBit_two_pow, Fin.val_inj]
lemma ev_top {n : ℕ} (x : Fin n → ZMod 2) (i : Fin n) (r : ℕ)
    (hr : r < 2 ^ (i.val + 1)) (hi : r.testBit i.val = true)
    (hx : ∀ j : Fin n, j < i → x j = 0) : ev x r = x i := by
  rw [ev, Finset.sum_eq_single i]
  · simp [bit, hi]
  · intro j _ hji
    by_cases hlt : j < i
    · simp [hx j hlt]
    · have hpow : 2 ^ (i.val + 1) ≤ 2 ^ j.val := Nat.pow_le_pow_right (by decide) (by omega)
      simp [bit, Nat.testBit_lt_two_pow (hr.trans_le hpow)]
  · simp
lemma ev_xorList {n : ℕ} (x : Fin n → ZMod 2) (rs : List ℕ) :
    ev x (xorList rs) = (rs.map (ev x)).sum := by
  induction rs with
  | nil => exact ev_zero x
  | cons a as ih => simp only [xorList, ev_xor, ih, List.map_cons, List.sum_cons]

/-- Read a matrix in row-major order. -/
def flat {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) (i : Fin (m*n)) : ZMod 2 :=
  M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

def unflat {m n : ℕ} (x : Fin (m*n) → ZMod 2) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => x (finProdFinEquiv (i,j))

lemma unflat_flat {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    unflat (flat M) = M := by ext i j; simp [unflat, flat]

lemma flat_unflat {m n : ℕ} (x : Fin (m*n) → ZMod 2) :
    flat (unflat x) = x := by
  funext i
  change x (finProdFinEquiv (finProdFinEquiv.symm i)) = x i
  rw [Equiv.apply_symm_apply]

/-- Frobenius pairing, with no nondegeneracy assumptions. -/
def pairing {m n : ℕ} (A B : Matrix (Fin m) (Fin n) (ZMod 2)) : ZMod 2 :=
  ∑ i, ∑ j, A i j * B i j

lemma ev_flat {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) (r : ℕ) :
    ev (flat M) r = pairing (unflat (fun i => bit r i.val)) M := by
  rw [ev, ← finProdFinEquiv.sum_comp]
  rw [Fintype.sum_prod_type]
  simp [pairing, flat, unflat]

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


/-- Row slices of one packed rectangular matrix. -/
def slices (m n x : ℕ) : Vector ℕ m :=
  Vector.ofFn (fun i => (x >>> (n * i.val)) % 2^n)

lemma decode_slices (m n x : ℕ) :
    rectDecode n (slices m n x) = unflat (fun i => bit x i.val) := by
  funext i j
  simp only [rectDecode, slices, get_ofFn, unflat, bit]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp only [j.isLt, decide_true, Bool.true_and]
  change (if x.testBit (n * i.val + j.val) then (1 : ZMod 2) else 0) =
    (if x.testBit (j.val + n * i.val) then 1 else 0)
  rw [Nat.add_comm]

lemma pairing_add {m n : ℕ} (A B C : Matrix (Fin m) (Fin n) (ZMod 2)) :
    pairing A (B+C) = pairing A B + pairing A C := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

lemma pairing_smul {m n : ℕ} (c : ZMod 2) (A B : Matrix (Fin m) (Fin n) (ZMod 2)) :
    pairing A (c • B) = c * pairing A B := by
  simp [pairing, Finset.mul_sum, mul_left_comm]

lemma pairing_span {m n d : ℕ} (B : Fin d → Matrix (Fin m) (Fin n) (ZMod 2))
    (W : Matrix (Fin m) (Fin n) (ZMod 2))
    (h : ∀ i, pairing W (B i) = 0) (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (hM : M ∈ Submodule.span (ZMod 2) (Set.range B)) : pairing W M = 0 := by
  induction hM using Submodule.span_induction with
  | mem x hx => obtain ⟨i,rfl⟩ := hx; exact h i
  | zero => simp [pairing]
  | add x y _ _ hx hy => rw [pairing_add, hx, hy, add_zero]
  | smul c x _ hx => rw [pairing_smul, hx, mul_zero]

lemma pairing_transpose {m n : ℕ} (A B : Matrix (Fin m) (Fin n) (ZMod 2)) :
    pairing Aᵀ Bᵀ = pairing A B := by
  exact Finset.sum_comm

lemma pairing_mul_left {m n k : ℕ}
    (W : Matrix (Fin m) (Fin k) (ZMod 2))
    (U : Matrix (Fin m) (Fin n) (ZMod 2))
    (S : Matrix (Fin n) (Fin k) (ZMod 2)) :
    pairing W (U*S) = pairing (Uᵀ*W) S := by
  simp only [pairing, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul,
    Matrix.transpose_apply]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma pairing_mul_right {m n k : ℕ}
    (W : Matrix (Fin m) (Fin k) (ZMod 2))
    (S : Matrix (Fin m) (Fin n) (ZMod 2))
    (U : Matrix (Fin n) (Fin k) (ZMod 2)) :
    pairing W (S*U) = pairing (W*Uᵀ) S := by
  rw [← pairing_transpose W (S*U), Matrix.transpose_mul, pairing_mul_left]
  simpa only [Matrix.transpose_transpose, Matrix.transpose_mul] using
    (pairing_transpose (W*Uᵀ) S)

lemma pairing_mixed_adjoint (W U : MixedMatrix) (S : RestrictionMatrix) :
    pairing W (U * pairingAdjoint S) =
      pairing (restrictionPairing * Wᵀ * (U * pairingInverse)) S := by
  rw [pairingAdjoint, ← Matrix.mul_assoc, ← Matrix.mul_assoc, pairing_mul_right,
    pairing_mul_left]
  rw [← pairing_transpose _ Sᵀ, Matrix.transpose_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- Scalar product of two finite binary masks. -/
def dotMask : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n+1, x, y => (if x.testBit 0 && y.testBit 0 then 1 else 0) ^^^
      dotMask n (x >>> 1) (y >>> 1)

lemma bit_dotMask (n x y : ℕ) :
    bit (dotMask n x y) 0 = ev (fun i : Fin n => bit y i.val) x := by
  induction n generalizing x y with
  | zero => simp [dotMask, ev, bit]
  | succ n ih =>
    rw [dotMask, bit_xor, ih]
    simp only [ev, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
    congr 1
    · cases hx : x.testBit 0 <;> cases hy : y.testBit 0 <;> simp [bit, hx, hy]
    · simp only [bit, Nat.testBit_shiftRight, Nat.add_comm 1]

lemma ev_scan {n d : ℕ} (x : Fin n → ZMod 2) (c : ℕ) (rs : Vector ℕ d) :
    ev x (scan c rs.toList) = ∑ i : Fin d, bit c i.val * ev x (rs.get i) := by
  rw [← ofFn_get, scan_ofFn, ev_xorList, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  cases h : c.testBit i.val <;> simp [h, bit, ev_zero]

/-- Every checked elimination row is a consequence of its source rows. -/
theorem trace_sound {n d : ℕ} (x : Fin n → ZMod 2)
    (rows base : Vector ℕ d) (parents : Vector (List ℕ) d)
    (hbase : ∀ i, ev x (base.get i) = 0)
    (htrace : ∀ i : Fin d,
      (∀ j ∈ parents.get i, j < i.val) ∧
      rows.get i = base.get i ^^^
        xorList ((parents.get i).map (fun j => rows.toArray[j]!))) :
    ∀ i, ev x (rows.get i) = 0 := by
  suffices ∀ k (hk : k < d), ev x (rows.get ⟨k,hk⟩) = 0 by
    intro i
    exact this i.val i.isLt
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    let i : Fin d := ⟨k,hk⟩
    obtain ⟨hlt, heq⟩ := htrace i
    rw [heq, ev_xor, hbase, zero_add, ev_xorList, List.map_map]
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    have hjd : j < d := (hlt j hj).trans i.isLt
    change ev x (rows.toArray[j]!) = 0
    rw [getElem!_pos rows.toArray j (by simpa using hjd)]
    exact ih j (hlt j hj) hjd

/-- The reduced equations reconstruct a vector from the displayed free entries. -/
theorem reconstruct {n d : ℕ} (x : Fin n → ZMod 2)
    (free : Vector (Fin n) d) (bs : Vector ℕ d) (rs : Fin n → ℕ)
    (hz : ∀ i, ev x (rs i) = 0)
    (heq : ∀ i : Fin n, rs i = 2 ^ i.val ^^^
      xorList (List.ofFn (fun k : Fin d =>
        if (bs.get k).testBit i.val then 2 ^ (free.get k).val else 0))) :
    x = ∑ k : Fin d, x (free.get k) • (fun i => bit (bs.get k) i.val) := by
  funext i
  have h := hz i
  rw [heq, ev_xor, ev_unit, ev_xorList, List.map_ofFn, List.sum_ofFn] at h
  have hs : (∑ k : Fin d, ev x
      (if (bs.get k).testBit i.val then 2 ^ (free.get k).val else 0)) =
      (∑ k : Fin d, x (free.get k) * bit (bs.get k) i.val) := by
    apply Finset.sum_congr rfl
    intro k _
    cases hk : (bs.get k).testBit i.val <;> simp [hk, ev_zero, ev_unit, bit]
  simp only [Function.comp_def] at h
  rw [hs] at h
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    (CharTwo.add_eq_zero.mp h)

lemma unflat_sum {m n d : ℕ} (f : Fin d → Fin (m*n) → ZMod 2) :
    unflat (∑ i, f i) = ∑ i, unflat (f i) := by ext i j; simp [unflat, Matrix.sum_apply]

lemma unflat_smul {m n : ℕ} (c : ZMod 2) (x : Fin (m*n) → ZMod 2) :
    unflat (c • x) = c • unflat x := rfl

/-- A packed combination of the published matrices lies in their span. -/
theorem combination_mem {m n d : ℕ} (B : Fin d → Matrix (Fin m) (Fin n) (ZMod 2))
    (packed : Vector ℕ d) (hB : ∀ k, unflat (fun i => bit (packed.get k) i.val) = B k)
    (c : ℕ) : unflat (fun i : Fin (m*n) => bit (scan c packed.toList) i.val) ∈
      Submodule.span (ZMod 2) (Set.range B) := by
  have heq : unflat (fun i : Fin (m*n) => bit (scan c packed.toList) i.val) =
      ∑ k : Fin d, bit c k.val • B k := by
    ext i j
    simp only [unflat, bit_scan, ev, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [← hB k]
    rfl
  rw [heq]
  apply Submodule.sum_mem
  intro k _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,rfl⟩)

/-- Packed rectangular multiplication, scanning each binary row. -/
def mulRows {m n : ℕ} (xs : Vector ℕ m) (ys : Vector ℕ n) : Vector ℕ m :=
  Vector.ofFn (fun i => scan (xs.get i) ys.toList)

lemma decode_mulRows {m n : ℕ} (k : ℕ) (xs : Vector ℕ m) (ys : Vector ℕ n) :
    rectDecode k (mulRows xs ys) = rectDecode n xs * rectDecode k ys := by
  rw [← rectDecode_product]
  congr 1
  apply congrArg Vector.ofFn
  funext i
  rw [← ofFn_get, scan_ofFn]
  rfl

/-- Packed transpose, with its number of columns specified. -/
def transRows {m : ℕ} (n : ℕ) (xs : Vector ℕ m) : Vector ℕ n :=
  Vector.ofFn (fun j => xorList (List.ofFn (fun i : Fin m =>
    if (xs.get i).testBit j.val then 2 ^ i.val else 0)))

set_option linter.unusedSimpArgs false in
lemma decode_transRows {m : ℕ} (n : ℕ) (xs : Vector ℕ m) :
    rectDecode m (transRows n xs) = (rectDecode n xs)ᵀ := by
  funext j i
  simp only [rectDecode, transRows, get_ofFn, bit_xorList, List.map_ofFn,
    List.sum_ofFn, Matrix.transpose_apply, Function.comp_def]
  rw [Finset.sum_eq_single i]
  · cases h : (xs.get i).testBit j.val <;> simp [h, bit, Nat.testBit_two_pow]
  · intro a _ hai
    cases h : (xs.get a).testBit j.val <;>
      simp [h, bit, Nat.testBit_two_pow, hai, Fin.val_inj]
  · simp

lemma ev_packed_pairing {m n : ℕ} (x y : ℕ) :
    bit (dotMask (m*n) x y) 0 =
      pairing (rectDecode n (slices m n x)) (rectDecode n (slices m n y)) := by
  rw [bit_dotMask, ← flat_unflat (fun i : Fin (m*n) => bit y i.val), ev_flat,
    ← decode_slices, ← decode_slices]

lemma decode_xor_rows {m : ℕ} (n : ℕ) (xs ys : Vector ℕ m) :
    rectDecode n (Vector.ofFn (fun i => xs.get i ^^^ ys.get i)) =
      rectDecode n xs + rectDecode n ys := by
  ext i j
  simp only [rectDecode, get_ofFn, Matrix.add_apply, bit_xor]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.FiniteAlgebra

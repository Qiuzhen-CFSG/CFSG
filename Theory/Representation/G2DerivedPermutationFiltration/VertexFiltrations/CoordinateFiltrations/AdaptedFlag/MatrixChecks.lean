module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.Interface

/-!
# Kernel certificates for the adapted binary matrices

The packed vectors in `Data` are checked using bitwise XOR. The proved decoding
lemmas identify XOR with addition in `ZMod 2`; thus the finite integer checks
imply genuine matrix inverse and generator-action identities. The bounds on
packed columns prove preservation of every published initial coordinate segment.
The resulting linear equivalence intertwines the actual permutation action
with `actionMatrix`, using the inverse-permutation convention of `Coordinates`.

These certificates are a coordinate ingredient for Aschbacher–Smith G.7.2(3),
printed pp.347–348. The original witnesses and their ATLAS attribution are
recorded in `CoordinateFiltrations.Data`; all identities used here are checked
in Lean's kernel.
-/

@[expose] public section

namespace G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.AdaptedFlag

open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

def xorList : List ℕ → ℕ
  | [] => 0
  | a :: l => a ^^^ xorList l

theorem bit_xor (a b x : ℕ) : bit (a ^^^ b) x = bit a x + bit b x := by
  unfold bit
  rw [Nat.testBit_xor]
  cases a.testBit x <;> cases b.testBit x <;> decide

theorem bit_zero (x : ℕ) : bit 0 x = 0 := by simp [bit]

theorem bit_xorList (l : List ℕ) (x : ℕ) :
    bit (xorList l) x = (l.map (fun a => bit a x)).sum := by
  induction l with
  | nil => exact bit_zero x
  | cons a l ih => simp [xorList, bit_xor, ih]

def combine {n : ℕ} (c : Fin n → ℕ) (b : Fin n → Bool) : ℕ :=
  xorList (List.ofFn fun y => if b y then c y else 0)

theorem bit_combine {n : ℕ} (c : Fin n → ℕ) (b : Fin n → Bool) (x : ℕ) :
    bit (combine c b) x = ∑ y, bit (c y) x * (if b y then 1 else 0) := by
  rw [combine, bit_xorList, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro y _
  cases h : b y <;> simp [h, bit_zero]

theorem bit_power (x y : ℕ) : bit (2 ^ y) x = if y = x then 1 else 0 := by
  simp [bit, Nat.testBit_two_pow]

def pack {n : ℕ} (b : Fin n → Bool) := combine (fun x => 2 ^ x.val) b

theorem bit_pack {n : ℕ} (b : Fin n → Bool) (x : Fin n) :
    bit (pack b) x.val = if b x then 1 else 0 := by
  rw [pack, bit_combine]
  simp only [bit_power, Fin.val_inj, ite_mul, one_mul, zero_mul]
  simp

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem packed_inverse : ∀ (i : Fin 2) (y : Fin 63),
    combine (basis i) (fun z => (inverseRows i z).testBit y.val) = 2 ^ y.val := by
  decide +kernel

end G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.AdaptedFlag

namespace G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.AdaptedFlag

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem packed_action : ∀ (i j : Fin 2) (y : Fin 63),
    combine (basis i) (fun z => (actionColumns i j y).testBit z.val) =
      pack (fun x : Fin 63 => (basis i y).testBit (inverseTable i j x).val) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem packed_upper : ∀ (i : Fin 2) (m : Fin 13) (j : Fin 2) (y : Fin 63),
    y.val < cut i m.val → actionColumns i j y < 2 ^ cut i m.val := by
  decide +kernel

theorem basis_mul_inverse (i : Fin 2) : basisMatrix i * inverseMatrix i = 1 := by
  ext x y
  have h := congrArg (fun a => bit a x.val) (packed_inverse i y)
  rw [bit_combine, bit_power] at h
  simpa only [basisMatrix, inverseMatrix, bit, Matrix.mul_apply, Matrix.one_apply,
    Fin.val_inj, eq_comm] using h

theorem inverse_mul_basis (i : Fin 2) : inverseMatrix i * basisMatrix i = 1 :=
  (mul_eq_one_comm (a := basisMatrix i) (b := inverseMatrix i)).mp (basis_mul_inverse i)

theorem basis_mul_action (i j : Fin 2) :
    basisMatrix i * actionMatrix i j =
      fun x y => basisMatrix i (inverseTable i j x) y := by
  ext x y
  have h := congrArg (fun a => bit a x.val) (packed_action i j y)
  rw [bit_combine, bit_pack] at h
  exact h

theorem cut_eq_full (i : Fin 2) (m : ℕ) (hm : 13 ≤ m) : cut i m = 63 := by
  unfold cut
  split <;> rw [List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega)]
  all_goals rfl

theorem upper (i : Fin 2) (m : ℕ) (j : Fin 2) (x y : Fin 63)
    (hx : cut i m ≤ x.val) (hy : y.val < cut i m) : actionMatrix i j x y = 0 := by
  by_cases hm : m < 13
  · have h := packed_upper i ⟨m, hm⟩ j y hy
    have h' : actionColumns i j y < 2 ^ x.val :=
      h.trans_le (Nat.pow_le_pow_right (by decide) hx)
    simp [actionMatrix, bit, Nat.testBit_lt_two_pow h']
  · rw [cut_eq_full i m (by omega)] at hx
    omega

def basisCoordinates (i : Fin 2) : Space ≃ₗ[ZMod 2] (Fin 63 → ZMod 2) :=
  { (inverseMatrix i).mulVecLin with
    invFun := (basisMatrix i).mulVec
    left_inv := fun v => by
      change (basisMatrix i).mulVec ((inverseMatrix i).mulVec v) = v
      rw [Matrix.mulVec_mulVec, basis_mul_inverse, Matrix.one_mulVec]
    right_inv := fun v => by
      change (inverseMatrix i).mulVec ((basisMatrix i).mulVec v) = v
      rw [Matrix.mulVec_mulVec, inverse_mul_basis, Matrix.one_mulVec] }

set_option maxRecDepth 8192 in
theorem basisCoordinates_symm_apply (i : Fin 2) (v : Space) :
    (basisCoordinates i).symm v = (basisMatrix i).mulVec v := rfl

theorem basisCoordinates_generator (i j : Fin 2) (v : Space) :
    basisCoordinates i (representation i (FreeGroup.of j) v) =
      (actionMatrix i j).mulVec (basisCoordinates i v) := by
  have h (w : Space) :
      (basisMatrix i).mulVec ((actionMatrix i j).mulVec w) =
        representation i (FreeGroup.of j) ((basisMatrix i).mulVec w) := by
    rw [Matrix.mulVec_mulVec, basis_mul_action]
    ext x
    rw [representation_of_apply]
    rfl
  apply (basisCoordinates i).symm.injective
  rw [LinearEquiv.symm_apply_apply, basisCoordinates_symm_apply, h,
    ← basisCoordinates_symm_apply, LinearEquiv.symm_apply_apply]

end G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations.AdaptedFlag

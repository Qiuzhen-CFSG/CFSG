module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.Data

/-!
# Checked adapted coordinates for the 198-dimensional candidates

Packed XOR is proved to decode to addition over F₂. The integer certificates
therefore prove a genuine basis inverse and conjugacy of the two matrices,
including their off-diagonal blocks. Bounds on columns prove flag invariance.
This verifies the candidate linear algebra, not the M22 model comparison or
simplicity of the diagonal factors.

The decoding argument follows the existing G₂ vertex-filtration certificate.
Source: Guralnick--Malle I, Proposition 5.1, pp.15--16.
-/

@[expose] public section
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
namespace MatrixChecks

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


/-- Traverse stored columns once, rather than repeatedly indexing them. -/
def combineListFrom : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | a :: l, mask, start =>
      (if mask.testBit start then a else 0) ^^^ combineListFrom l mask (start + 1)

def combineList (l : List ℕ) (mask : ℕ) : ℕ := combineListFrom l mask 0

private theorem combineListFrom_eq (l : List ℕ) (mask start : ℕ) :
    combineListFrom l mask start =
      xorList (l.mapIdx fun j a => if mask.testBit (start + j) then a else 0) := by
  induction l generalizing start with
  | nil => rfl
  | cons a l ih =>
    rw [combineListFrom, List.mapIdx_cons]
    simp only [Nat.add_zero, xorList]
    rw [ih]
    simp only [Nat.add_assoc, Nat.add_comm 1]

theorem combineList_eq (l : List ℕ) (n : ℕ) (hn : l.length = n) (mask : ℕ) :
    combineList l mask = combine (fun j : Fin n => l[j.val]?.getD 0)
      (fun j => mask.testBit j.val) := by
  subst n
  rw [combineList, combineListFrom_eq]
  unfold combine
  simp only [Nat.zero_add]
  congr 1
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp only [List.getElem_mapIdx, List.getElem_ofFn]
    simp only [List.length_mapIdx] at hj
    rw [List.getElem?_eq_getElem hj]
    rfl

theorem bit_combineList (l : List ℕ) (n : ℕ) (hn : l.length = n)
    (mask x : ℕ) :
    bit (combineList l mask) x =
      ∑ j : Fin n, bit (l[j.val]?.getD 0) x * bit mask j.val := by
  rw [combineList_eq l n hn, bit_combine]
  rfl

set_option maxRecDepth 8192 in
private theorem packed_inverse : ∀ (i : Fin 2) (y : Fin 198),
    combineList (basisList i) (inverseColumns i y) = 2 ^ y.val := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_action : ∀ (i j : Fin 2) (y : Fin 198),
    combineList (basisList i) (actionColumns i j y) =
      combineList (generatorColumnList i j) (basis i y) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_upper : ∀ (i : Fin 2) (m : Fin 9) (j : Fin 2) (y : Fin 198),
    y.val < cut i m.val → actionColumns i j y < 2 ^ cut i m.val := by
  decide +kernel

theorem basis_mul_inverse (i : Fin 2) : basisMatrix i * inverseMatrix i = 1 := by
  ext x y
  have h := congrArg (fun a => bit a x.val) (packed_inverse i y)
  rw [bit_combineList _ 198 (basisList_length i), bit_power] at h
  simpa only [basisMatrix, inverseMatrix, basis, bit, Matrix.mul_apply, Matrix.one_apply,
    Fin.val_inj, eq_comm] using h

theorem inverse_mul_basis (i : Fin 2) : inverseMatrix i * basisMatrix i = 1 :=
  (mul_eq_one_comm (a := basisMatrix i) (b := inverseMatrix i)).mp (basis_mul_inverse i)

theorem basis_mul_action (i j : Fin 2) :
    basisMatrix i * actionMatrix i j = generatorMatrix i j * basisMatrix i := by
  ext x y
  have h := congrArg (fun a => bit a x.val) (packed_action i j y)
  rw [bit_combineList _ 198 (basisList_length i),
    bit_combineList _ 198 (generatorColumnList_length i j)] at h
  exact h

theorem cut_eq_full (i : Fin 2) (m : ℕ) (hm : 9 ≤ m) : cut i m = 198 := by
  unfold cut
  split <;> rw [List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega)]
  all_goals rfl

theorem upper (i : Fin 2) (m : ℕ) (j : Fin 2) (x y : Fin 198)
    (hx : cut i m ≤ x.val) (hy : y.val < cut i m) : actionMatrix i j x y = 0 := by
  by_cases hm : m < 9
  · have h := packed_upper i ⟨m, hm⟩ j y hy
    have h' : actionColumns i j y < 2 ^ x.val :=
      h.trans_le (Nat.pow_le_pow_right (by decide) hx)
    simp [actionMatrix, bit, Nat.testBit_lt_two_pow h']
  · rw [cut_eq_full i m (by omega)] at hx
    omega

def basisCoordinates (i : Fin 2) : Space ≃ₗ[ZMod 2] Space :=
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
    basisCoordinates i ((generatorMatrix i j).mulVec v) =
      (actionMatrix i j).mulVec (basisCoordinates i v) := by
  have h (w : Space) :
      (basisMatrix i).mulVec ((actionMatrix i j).mulVec w) =
        (generatorMatrix i j).mulVec ((basisMatrix i).mulVec w) := by
    simp only [Matrix.mulVec_mulVec, basis_mul_action]
  apply (basisCoordinates i).symm.injective
  rw [LinearEquiv.symm_apply_apply, basisCoordinates_symm_apply, h,
    ← basisCoordinates_symm_apply, LinearEquiv.symm_apply_apply]

end MatrixChecks
end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration

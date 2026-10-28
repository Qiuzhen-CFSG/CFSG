module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.InducedQuotients.Data

/-!
# Checked basis and block matrices for the 120-dimensional tensor model

XOR decodes to addition over F₂. The packed inverse and action checks give
an invertible adapted basis, preserving every extension block. The checked
column bounds give the proposed upper block triangular shape.

The decoding proof adapts the existing M₂₂ Hermitian `MatrixChecks` in
this repository. These checks prove linear algebra on the displayed data;
the native action comparison and simple-factor proofs are separate inputs.
Source context: James, J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
namespace Representation.MathieuSmall.M12DegreeGap.InducedQuotients.CertificateData
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
private theorem packed_inverse : ∀ y : Fin 120,
    combineList basisList (inverseColumns y) = 2 ^ y.val := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_action : ∀ (j : Fin 2) (y : Fin 120),
    combineList basisList (actionColumns j y) =
      combineList (generatorColumnList j) (basis y) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem packed_upper : ∀ (m : Fin 8) (j : Fin 2) (y : Fin 120),
    y.val < cut m.val → actionColumns j y < 2 ^ cut m.val := by
  decide +kernel

theorem basis_mul_inverse : basisMatrix * inverseMatrix = 1 := by
  ext x y
  have h := congrArg (fun a => bit a x.val) (packed_inverse y)
  rw [bit_combineList _ 120 basisList_length, bit_power] at h
  simpa only [basisMatrix, inverseMatrix, basis, bit, Matrix.mul_apply, Matrix.one_apply,
    Fin.val_inj, eq_comm] using h

set_option maxRecDepth 8192 in
theorem inverse_mul_basis : inverseMatrix * basisMatrix = 1 :=
  (mul_eq_one_comm (a := basisMatrix) (b := inverseMatrix)).mp basis_mul_inverse

theorem basis_mul_action (j : Fin 2) :
    basisMatrix * actionMatrix j = generatorMatrix j * basisMatrix := by
  ext x y
  have h := congrArg (fun a => bit a x.val) (packed_action j y)
  rw [bit_combineList _ 120 basisList_length,
    bit_combineList _ 120 (generatorColumnList_length j)] at h
  exact h

theorem cut_eq_full (m : ℕ) (hm : 8 ≤ m) : cut m = 120 := by
  unfold cut
  rw [List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega)]
  rfl

theorem upper (m : ℕ) (j : Fin 2) (x y : Fin 120)
    (hx : cut m ≤ x.val) (hy : y.val < cut m) : actionMatrix j x y = 0 := by
  by_cases hm : m < 8
  · have h := packed_upper ⟨m, hm⟩ j y hy
    have h' : actionColumns j y < 2 ^ x.val :=
      h.trans_le (Nat.pow_le_pow_right (by decide) hx)
    simp [actionMatrix, bit, Nat.testBit_lt_two_pow h']
  · rw [cut_eq_full m (by omega)] at hx
    omega

def basisCoordinates : Space ≃ₗ[ZMod 2] Space :=
  { inverseMatrix.mulVecLin with
    invFun := basisMatrix.mulVec
    left_inv := fun v => by
      change basisMatrix.mulVec (inverseMatrix.mulVec v) = v
      rw [Matrix.mulVec_mulVec, basis_mul_inverse, Matrix.one_mulVec]
    right_inv := fun v => by
      change inverseMatrix.mulVec (basisMatrix.mulVec v) = v
      rw [Matrix.mulVec_mulVec, inverse_mul_basis, Matrix.one_mulVec] }

set_option maxRecDepth 8192 in
theorem basisCoordinates_symm_apply (v : Space) :
    basisCoordinates.symm v = basisMatrix.mulVec v := rfl

theorem basisCoordinates_generator (j : Fin 2) (v : Space) :
    basisCoordinates ((generatorMatrix j).mulVec v) =
      (actionMatrix j).mulVec (basisCoordinates v) := by
  have h (w : Space) :
      basisMatrix.mulVec ((actionMatrix j).mulVec w) =
        (generatorMatrix j).mulVec (basisMatrix.mulVec w) := by
    simp only [Matrix.mulVec_mulVec, basis_mul_action]
  apply basisCoordinates.symm.injective
  rw [LinearEquiv.symm_apply_apply, basisCoordinates_symm_apply, h,
    ← basisCoordinates_symm_apply, LinearEquiv.symm_apply_apply]

end MatrixChecks
end Representation.MathieuSmall.M12DegreeGap.InducedQuotients.CertificateData

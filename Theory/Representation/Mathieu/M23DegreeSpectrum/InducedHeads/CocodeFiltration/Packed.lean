module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.Data

/-!
# Packed binary linear combinations for the M23 filtration

The integer XOR checker decodes to ordinary matrix multiplication over F₂.
Adapted from the project's M22 HermitianFiltration/MatrixChecks.lean;
kept separate from the concrete checks so each certificate can be measured
without re-elaborating the mathematical soundness proof.
-/

@[expose] public section
namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration
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


end MatrixChecks
end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration

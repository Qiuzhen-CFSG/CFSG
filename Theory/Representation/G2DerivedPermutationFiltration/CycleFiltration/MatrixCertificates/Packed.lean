module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.MatrixCertificates.Data

/-!
# Decoding binary matrix certificates

XOR of packed columns is addition over `ZMod 2`. The decoding identity below
turns finite natural-number certificates into ordinary matrix identities.
This supports the saved incidence calculation for Aschbacher–Smith G.7.2(3).
-/

@[expose] public section
namespace G2DerivedPermutationFiltration.CycleData.Certificate

def xorList : List ℕ → ℕ
  | [] => 0
  | a :: l => a ^^^ xorList l

theorem bit_xor (a b x : ℕ) : bit (a ^^^ b) x = bit a x + bit b x := by
  unfold bit
  rw [Nat.testBit_xor]
  cases a.testBit x <;> cases b.testBit x <;> decide

theorem bit_zero (x : ℕ) : bit 0 x = 0 := by simp [bit]

private theorem bit_xorList (l : List ℕ) (x : ℕ) :
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

/-- Pack from low to high bits by a linear fold, avoiding repeated powers. -/
def pack {n : ℕ} (b : Fin n → Bool) : ℕ := (List.ofFn b).foldr Nat.bit 0

theorem testBit_pack {n : ℕ} (b : Fin n → Bool) (x : Fin n) :
    (pack b).testBit x.val = b x := by
  induction n with
  | zero => exact Fin.elim0 x
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) x
    · simp [pack, List.ofFn_succ]
    · simpa only [pack, List.ofFn_succ, List.foldr_cons, Fin.val_succ,
        Nat.testBit_bit_succ] using ih (fun j => b j.succ) i

theorem bit_pack {n : ℕ} (b : Fin n → Bool) (x : Fin n) :
    bit (pack b) x.val = if b x then 1 else 0 := by
  rw [bit, testBit_pack]

theorem columns_mul_apply {m n p : ℕ} (a : Fin n → ℕ) (b : Fin p → ℕ)
    (i : Fin m) (j : Fin p) :
    (columns (m := m) a * columns (m := n) b) i j = bit (combine a (fun k => (b j).testBit k.val)) i.val := by
  rw [bit_combine]
  rfl

end G2DerivedPermutationFiltration.CycleData.Certificate
